#![forbid(unsafe_code)]

//! Dana v0.7.0 capability-gated local HTTP (`LocalHttpAllow`) and Unix domain socket
//! (`LocalSocketAllow`) tests:
//! - Compile-time authority/path & anti-SSRF rejections (plus `HttpsAllow` plaintext refusal)
//! - Runtime loopback port pinning, redirect blocking, header/CRLF validation, and UDS symlink guards
//! - Privacy tags, `Secret` header redaction, `dana.policy` allow/forbid, `--allow-export`, and `dry-run`
//! - Offline `LocalHttp.fake` / `LocalSocket.fake` spec tests (`VM == --oracle`)
//! - Live loopback `TcpListener` (`ready:<file>` + `GET`/`POST`/`PUT`/`DELETE`) & Unix socket E2E

use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

use dana::base::{DiagCode, SourceMap};
use dana::check::{check_module, parse_policy};
use dana::core::syntax::BugKind;
use dana::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use dana::syntax::parse_module;
use dana::vm::{VmConfig, run_exec_program_vm, run_program_tests_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

static TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> TestResult<Self> {
        let id = TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let sys_tmp = std::env::temp_dir();
        let base = if sys_tmp.as_os_str().len() > 60 {
            PathBuf::from("/tmp")
        } else {
            sys_tmp
        };
        let path = base.join(format!("d7_{prefix}_{pid}_{id}"));
        if path.exists() {
            fs::remove_dir_all(&path)?;
        }
        fs::create_dir_all(&path)?;
        Ok(Self { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn check_src_with_policy(
    src: &str,
    pol_src: Option<&str>,
) -> Result<dana::check::CheckedProgram, Vec<dana::base::Diagnostic>> {
    let mut sm = SourceMap::new();
    let policy = match pol_src {
        Some(ps) => {
            let pid = sm.add_file("dana.policy", ps.to_string());
            Some(parse_policy(pid, ps).map_err(|d| vec![d])?)
        }
        None => None,
    };
    let fid = sm.add_file("test_v07.dana", src.to_string());
    let m = parse_module(fid, src).map_err(|d| vec![d])?;
    check_module(fid, m, policy, &sm)
}

#[derive(Clone, Debug)]
struct CapturedHttpReq {
    method: String,
    path: String,
    headers: Vec<(String, String)>,
    body: String,
}

fn read_http_req_from_stream<S: Read + Write>(
    stream: S,
    status_line: &str,
    resp_headers: &str,
    resp_body: &[u8],
) -> Option<CapturedHttpReq> {
    let mut reader = BufReader::new(stream);
    let mut req_line = String::new();
    if reader.read_line(&mut req_line).ok()? == 0 {
        return None;
    }
    let mut parts = req_line.split_ascii_whitespace();
    let method = parts.next()?.to_string();
    let path = parts.next()?.to_string();

    let mut content_len = 0usize;
    let mut headers = Vec::new();
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).ok()? == 0 {
            break;
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if let Some((k, v)) = trimmed.split_once(':') {
            if k.trim().eq_ignore_ascii_case("content-length") {
                content_len = v.trim().parse::<usize>().unwrap_or(0);
            }
            headers.push((k.trim().to_string(), v.trim().to_string()));
        }
    }

    let mut body_buf = vec![0u8; content_len];
    if content_len > 0 {
        reader.read_exact(&mut body_buf).ok()?;
    }
    let body = String::from_utf8_lossy(&body_buf).into_owned();

    let mut writer = reader.into_inner();
    let head = format!(
        "HTTP/1.1 {status_line}\r\n{resp_headers}Content-Length: {}\r\nConnection: close\r\n\r\n",
        resp_body.len()
    );
    let _ = writer.write_all(head.as_bytes());
    let _ = writer.write_all(resp_body);
    let _ = writer.flush();

    Some(CapturedHttpReq {
        method,
        path,
        headers,
        body,
    })
}

fn assert_oracle_vm_parity_with_cfg(src: &str, cfg: &RunConfig) -> TestResult<Vec<String>> {
    let checked = check_src_with_policy(src, None).map_err(|ds| format!("{ds:?}"))?;
    let ora = run_exec_program(&checked.exec, cfg);
    let vm = run_exec_program_vm(&checked.exec, cfg, &VmConfig::default());
    match (ora, vm) {
        (
            RunResult::Ok {
                exit_code: oc,
                stdout: os,
                stderr: oe,
            },
            RunResult::Ok {
                exit_code: vc,
                stdout: vs,
                stderr: ve,
            },
        ) => {
            assert_eq!(oc, vc, "exit code mismatch oracle={oc} vm={vc}");
            assert_eq!(os, vs, "stdout mismatch\noracle={os:?}\nvm={vs:?}");
            assert_eq!(oe, ve, "stderr mismatch\noracle={oe:?}\nvm={ve:?}");
            Ok(os)
        }
        (o, v) => Err(format!("engine mismatch or failure:\noracle={o:?}\nvm={v:?}").into()),
    }
}

// ===========================================================================
// 1. Compile-Time Authority / Path Validation & HttpsAllow Separation
// ===========================================================================

#[test]
fn v07_compile_time_rejects_portless_and_ssrf_targets() -> TestResult {
    let bad_http_targets = [
        "127.0.0.1",
        "localhost",
        "[::1]",
        "::1:8080",
        "0.0.0.0:8080",
        "[::]:8080",
        "[::ffff:127.0.0.1]:8080",
        "169.254.169.254:80",
        "10.0.0.1:8080",
        "172.16.0.1:8080",
        "192.168.1.1:8080",
        "example.com:80",
        "http://127.0.0.1:8080",
        "user@127.0.0.1:8080",
        "127.0.0.1:8080/path",
        "127.0.0.1:*",
        "127.0.0.1:0",
    ];
    for target in bad_http_targets {
        let src = format!(
            r#"
module BadHttpTarget
fn main(api: LocalHttpAllow("{target}")) : Int
  0
end
"#
        );
        let diags = check_src_with_policy(&src, None).err().ok_or_else(|| {
            format!("expected compile rejection for LocalHttpAllow(\"{target}\")")
        })?;
        assert!(
            diags.iter().any(|d| d.code() == DiagCode::CapabilityError),
            "expected CapabilityError for `{target}`, got: {diags:?}"
        );
    }

    let valid_http_targets = [
        r#""127.0.0.1:8091""#,
        r#""127.0.0.2:8091""#,
        r#""localhost:8091""#,
        r#""[::1]:8091""#,
        "MoShop",
    ];
    for target in valid_http_targets {
        let src = format!(
            r#"
module ValidHttpTarget
fn main(api: LocalHttpAllow({target})) : Int
  0
end
"#
        );
        check_src_with_policy(&src, None)
            .map_err(|ds| format!("expected `{target}` to pass check, got: {ds:?}"))?;
    }

    let bad_socket_targets = [
        "",
        "../escape.sock",
        "/tmp/../mo.sock",
        "http://127.0.0.1/s",
    ];
    for sock in bad_socket_targets {
        let src = format!(
            r#"
module BadSockTarget
fn main(sock: LocalSocketAllow("{sock}")) : Int
  0
end
"#
        );
        let diags = check_src_with_policy(&src, None)
            .err()
            .ok_or_else(|| format!("expected rejection for LocalSocketAllow(\"{sock}\")"))?;
        assert!(
            diags.iter().any(|d| d.code() == DiagCode::CapabilityError),
            "expected CapabilityError for `{sock}`, got: {diags:?}"
        );
    }

    // HttpsAllow MUST still reject plaintext http://127.0.0.1 URLs cleanly at runtime.
    let https_plain_src = r#"
module HttpsStillRejectsPlainHttp
fn main(api: HttpsAllow("127.0.0.1"), console: Console) : Int
  case api.get_json("http://127.0.0.1:8080/health")
    Ok(_): 0
    Error(msg):
      console.print("REJECT=#{msg}")
      1
  end
end
"#;
    let out = assert_oracle_vm_parity_with_cfg(https_plain_src, &RunConfig::default())?;
    assert_eq!(out.len(), 1);
    assert!(
        out[0].contains("REJECT=") && out[0].contains("HTTPS required"),
        "expected HttpsAllow to reject plain http://, got: {out:?}"
    );
    Ok(())
}

// ===========================================================================
// 2. Runtime Security Guards: Redirect Blocking, Mismatch, CRLF, Symlink UDS
// ===========================================================================

#[test]
fn v07_runtime_blocks_https_mismatches_redirects_and_uds_symlinks() -> TestResult {
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();
    let hits = Arc::new(Mutex::new(Vec::new()));
    let hits_srv = Arc::clone(&hits);

    let srv = thread::spawn(move || {
        for _ in 0..2 {
            let Ok((tcp, _)) = listener.accept() else {
                break;
            };
            if let Some(req) = read_http_req_from_stream(
                tcp,
                "302 Found",
                "Location: http://169.254.169.254/latest/meta-data\r\n",
                b"",
            ) && let Ok(mut g) = hits_srv.lock()
            {
                g.push(req);
            }
        }
    });

    let src = format!(
        r#"
module RuntimeSecurityGuards
fn main(api: LocalHttpAllow("127.0.0.1:{port}"), console: Console) : Int
  var checks = 0
  case api.get_json("https://127.0.0.1:{port}/health")
    Ok(_): Unit
    Error(e):
      console.print("HTTPS_REJECT=#{{e}}")
      checks = checks + 1
  end
  case api.get_json("http://127.0.0.1:65534/health")
    Ok(_): Unit
    Error(e):
      console.print("PORT_REJECT=#{{e}}")
      checks = checks + 1
  end
  case api.get_json("/health", headers: {{"Host": "169.254.169.254"}})
    Ok(_): Unit
    Error(e):
      console.print("HOST_HDR_REJECT=#{{e}}")
      checks = checks + 1
  end
  case api.get_json("/health", headers: {{"X-Test": "ok\r\nInjected: bad"}})
    Ok(_): Unit
    Error(e):
      console.print("CRLF_REJECT=#{{e}}")
      checks = checks + 1
  end
  case api.get_json("http://127.0.0.1:{port}/redir")
    Ok(_): Unit
    Error(e):
      console.print("REDIR_REJECT=#{{e}}")
      checks = checks + 1
  end
  checks
end
"#
    );

    let checked = check_src_with_policy(&src, None).map_err(|ds| format!("{ds:?}"))?;
    let cfg = RunConfig {
        live_io: true,
        ..RunConfig::default()
    };
    let ora = run_exec_program(&checked.exec, &cfg);
    let vm = run_exec_program_vm(&checked.exec, &cfg, &VmConfig::default());
    let _ = srv.join();

    for (label, res) in [("oracle", ora), ("vm", vm)] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 5, "{label} missed a guard: {stdout:?}");
                assert!(
                    stdout[0].contains("HTTPS_REJECT=") && stdout[0].contains("forbids `https://`"),
                    "{stdout:?}"
                );
                assert!(
                    stdout[1].contains("PORT_REJECT=") && stdout[1].contains("not permitted"),
                    "{stdout:?}"
                );
                assert!(
                    stdout[2].contains("HOST_HDR_REJECT=") && stdout[2].contains("`Host`"),
                    "{stdout:?}"
                );
                assert!(
                    stdout[3].contains("CRLF_REJECT=") && stdout[3].contains("CR/LF"),
                    "{stdout:?}"
                );
                assert!(
                    stdout[4].contains("REDIR_REJECT=") && stdout[4].contains("302"),
                    "{stdout:?}"
                );
            }
            other => return Err(format!("{label} unexpected result: {other:?}").into()),
        }
    }
    assert_eq!(
        hits.lock().map_err(|e| format!("{e}"))?.len(),
        2,
        "only the two 302 redirect checks should hit the wire (oracle + vm)"
    );

    // UDS regular-file and symlink guards (Unix only)
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        use std::os::unix::net::UnixListener;

        let tmp = TempDir::new("uds_guards")?;
        let reg_file = tmp.path().join("not_a_socket.txt");
        fs::write(&reg_file, "hello")?;

        let real_sock = tmp.path().join("real.sock");
        let _sock_listener = UnixListener::bind(&real_sock)?;
        let sym_sock = tmp.path().join("sym.sock");
        symlink(&real_sock, &sym_sock)?;

        let sock_src = format!(
            r#"
module SockGuards
fn main(
  s_reg: LocalSocketAllow("{reg}"),
  s_sym: LocalSocketAllow("{sym}"),
  console: Console
) : Int
  var ok_cnt = 0
  case s_reg.get_json("/health")
    Ok(_): Unit
    Error(e):
      console.print("REG=#{{e}}")
      ok_cnt = ok_cnt + 1
  end
  case s_sym.get_json("/health")
    Ok(_): Unit
    Error(e):
      console.print("SYM=#{{e}}")
      ok_cnt = ok_cnt + 1
  end
  ok_cnt
end
"#,
            reg = reg_file.display(),
            sym = sym_sock.display()
        );
        let checked_sock =
            check_src_with_policy(&sock_src, None).map_err(|ds| format!("{ds:?}"))?;
        let vm_cfg = RunConfig {
            live_io: true,
            ..RunConfig::default()
        };
        let vm = run_exec_program_vm(&checked_sock.exec, &vm_cfg, &VmConfig::default());
        match vm {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 2, "{stdout:?}");
                assert!(stdout[0].contains("not a Unix domain socket"), "{stdout:?}");
                assert!(stdout[1].contains("symlink"), "{stdout:?}");
            }
            other => return Err(format!("unexpected UDS guard result: {other:?}").into()),
        }
    }

    Ok(())
}

// ===========================================================================
// 3. Privacy, `dana.policy`, `--allow-export`, and `dry-run` Redaction
// ===========================================================================

#[test]
fn v07_privacy_policy_export_gate_and_dry_run_redaction() -> TestResult {
    // A. Static privacy blocks [pii] body/URL/header without `allows: [pii]`,
    //    while permitting `Secret(...)` in `headers:`.
    let pii_body_src = r#"
module PiiBodyDenied
schema Row
  email: Text [pii]
end
fn main(api: LocalHttpAllow("127.0.0.1:8091"), rows: Table(Row)) : Int
  _ = api.post_json("/items", body: rows)
  0
end
"#;
    let diags = check_src_with_policy(pii_body_src, None)
        .err()
        .ok_or("expected PrivacyError for [pii] table body without allows: [pii]")?;
    assert!(diags.iter().any(|d| d.code() == DiagCode::PrivacyError));

    // B. Policy forbid_local_http / forbid_local_socket & allow rules
    let base_src = r#"
module PolicyCheck
fn main(api: LocalHttpAllow("127.0.0.1:8091")) : Int
  0
end
"#;
    let forbid_pol = "version 1\nforbid local_http\n";
    let d_forbid = check_src_with_policy(base_src, Some(forbid_pol))
        .err()
        .ok_or("expected forbid local_http failure")?;
    assert!(d_forbid.iter().any(|d| d.code() == DiagCode::PrivacyError));

    let allow_other_port = "version 1\nallow local_http \"127.0.0.1:9999\" tags []\n";
    assert!(check_src_with_policy(base_src, Some(allow_other_port)).is_err());

    let allow_match = "version 1\nallow local_http \"127.0.0.1:8091\" tags []\n";
    assert!(check_src_with_policy(base_src, Some(allow_match)).is_ok());

    let sock_src =
        "module SockPol\nfn main(s: LocalSocketAllow(\"/tmp/mo.sock\")) : Int\n  0\nend\n";
    assert!(check_src_with_policy(sock_src, Some("version 1\nforbid local_socket\n")).is_err());

    // C. Live dry-run: GET works, POST/PUT/DELETE are suppressed with 0 server writes,
    //    and Secret bearer token never prints to stdout!
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();
    let requests = Arc::new(Mutex::new(Vec::new()));
    let reqs_srv = Arc::clone(&requests);

    let srv = thread::spawn(move || {
        for _ in 0..2 {
            let Ok((tcp, _)) = listener.accept() else {
                break;
            };
            if let Some(req) = read_http_req_from_stream(
                tcp,
                "200 OK",
                "Content-Type: application/json\r\n",
                br#"{"status":"ok"}"#,
            ) && let Ok(mut g) = reqs_srv.lock()
            {
                g.push(req);
            }
        }
    });

    let dry_src = format!(
        r#"
module DryRunLocalHttp
schema Item
  sku: Text [pii]
end
fn main(
  api: LocalHttpAllow("127.0.0.1:{port}", allows: [pii]),
  tok: Secret("mo_tok"),
  console: Console
) : Int
  h = try api.get_json("/health")
  rows = table
    | sku        |
    | "secret-1" |
  end
  _ = try api.post_json(
    "/products",
    body: rows,
    headers: {{"Authorization": "Bearer #{{tok}}", "X-Reason": "dry-check"}}
  )
  _ = try api.put_json("/products/1", body: "{{\"stock\":5}}")
  _ = try api.delete_json("/products/1", headers: {{"X-Reason": "cleanup"}})
  st = h.text_at("status")
  console.print("STATUS=#{{st}}")
  0
end
"#
    );
    let checked = check_src_with_policy(
        &dry_src,
        Some(&format!(
            "version 1\nallow local_http \"127.0.0.1:{port}\" tags [pii]\n"
        )),
    )
    .map_err(|ds| format!("{ds:?}"))?;

    // Without `--allow-export pii`, live run stops on ExportGateDenied
    let gate_stop = run_exec_program_vm(&checked.exec, &RunConfig::default(), &VmConfig::default());
    assert!(
        matches!(
            gate_stop,
            RunResult::Stopped {
                bug: dana::oracle::value::Bug {
                    kind: BugKind::ExportGateDenied,
                    ..
                },
                ..
            }
        ),
        "expected ExportGateDenied without --allow-export pii, got: {gate_stop:?}"
    );

    // Note `dry-run` permits GET + logs suppressed POST/PUT/DELETE without leaking tok
    let dry_cfg = RunConfig {
        live_io: true,
        dry_run: true,
        allow_export: dana::core::syntax::TagSet::singleton("pii"),
        ..RunConfig::default()
    };
    let dry_ora = run_exec_program(&checked.exec, &dry_cfg);
    let dry_vm = run_exec_program_vm(&checked.exec, &dry_cfg, &VmConfig::default());
    let _ = srv.join();

    match (dry_ora, dry_vm) {
        (RunResult::Ok { stdout: os, .. }, RunResult::Ok { stdout: vs, .. }) => {
            assert_eq!(os, vs);
            assert!(
                vs.iter()
                    .any(|l| l.contains("[DRY-RUN] would POST") && l.contains("Authorization"))
            );
            assert!(vs.iter().any(|l| l.contains("[DRY-RUN] would PUT")));
            assert!(vs.iter().any(|l| l.contains("[DRY-RUN] would DELETE")));
            assert!(vs.iter().any(|l| l == "STATUS=ok"));
            let joined = vs.join("\n");
            assert!(
                !joined.contains("env:mo_tok"),
                "secret value leaked in dry-run output: {joined}"
            );
            assert!(
                !joined.contains("secret-1"),
                "body payload leaked in dry-run output: {joined}"
            );
        }
        (o, v) => return Err(format!("dry-run failure: oracle={o:?} vm={v:?}").into()),
    }

    let captured = requests.lock().map_err(|e| format!("{e}"))?;
    assert_eq!(
        captured.len(),
        2,
        "only GET /health should hit server (oracle + vm)"
    );
    assert!(
        captured
            .iter()
            .all(|r| r.method == "GET" && r.path == "/health")
    );
    Ok(())
}

// ===========================================================================
// 4. Offline `LocalHttp.fake` & `LocalSocket.fake`
// ===========================================================================

#[test]
fn v07_offline_fakes_and_spec_only_enforcement() -> TestResult {
    let outside_spec = r#"
module FakeOutsideSpec
fn main() : Int
  _ = LocalHttp.fake("127.0.0.1:8091", responses: {})
  0
end
"#;
    assert!(check_src_with_policy(outside_spec, None).is_err());

    let src = r#"
module FakeLocalNetSpecs

schema Prod
  sku: Text
  stock: Int
end

fn run_sync(
  api: LocalHttpAllow(MoShop),
  admin: LocalSocketAllow(MoAdmin),
  console: Console
) : Int
  h = try api.get_json("/health")
  _ = try api.post_json("/products", body: "{\"sku\":\"p1\",\"stock\":7}")
  _ = try api.put_json("http://127.0.0.1:8091/products/p1", body: "{\"stock\":9}")
  _ = try api.delete_json("/products/old")
  _ = try admin.post_json("/flush", body: "{\"force\":true}")
  resp = try api.get_json("/products")
  (rows, _bad) = resp.parse_table("", as: Prod)
  st = h.text_at("status")
  console.print("STATUS=#{st} PRODS=#{rows.count()}")
  0
end

test "LocalHttp.fake and LocalSocket.fake record requests and bodies offline"
  api = LocalHttp.fake(MoShop, responses: {
    "GET /health": "{\"status\":\"ok\"}",
    "POST /products": "{\"ok\":true}",
    "PUT /products/p1": "",
    "DELETE /products/old": "",
    "GET /products": "[{\"sku\":\"p1\",\"stock\":9}]"
  })
  admin = LocalSocket.fake(MoAdmin, responses: {
    "POST /flush": "{\"flushed\":1}"
  })
  console = Console.fake()
  rc = run_sync(api, admin, console)
  assert rc == 0
  assert api.requests.size == 5
  assert api.request_bodies.size == 2
  assert admin.requests.first! == "/flush"
  assert console.printed_lines.first! == "STATUS=ok PRODS=1"
end
"#;
    let checked = check_src_with_policy(src, None).map_err(|ds| format!("{ds:?}"))?;
    let ora = run_program_tests(&checked.exec, None, &RunConfig::default());
    let vm = run_program_tests_vm(
        &checked.exec,
        None,
        &RunConfig::default(),
        &VmConfig::default(),
    );
    assert_eq!(ora.len(), 1);
    assert_eq!(vm.len(), 1);
    assert!(ora[0].passed, "{ora:?}");
    assert!(vm[0].passed, "{vm:?}");
    Ok(())
}

// ===========================================================================
// 5. Live Loopback TCP (`ready:<file>`) & Unix Domain Socket E2E (VM == Oracle)
// ===========================================================================

#[test]
fn v07_live_loopback_tcp_ready_file_and_uds_vm_oracle_parity() -> TestResult {
    let tmp = TempDir::new("live_tcp_uds")?;
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();
    let ready_path = tmp.path().join("ready.json");
    fs::write(
        &ready_path,
        format!(r#"{{"url":"http://127.0.0.1:{port}","port":{port}}}"#),
    )?;

    let tcp_captured = Arc::new(Mutex::new(Vec::new()));
    let tcp_srv_log = Arc::clone(&tcp_captured);
    let tcp_srv = thread::spawn(move || {
        // 4 requests per run * 2 engines (oracle + vm) = 8 requests
        for _ in 0..8 {
            let Ok((tcp, _)) = listener.accept() else {
                break;
            };
            // Peak-free dispatch: read request, return valid JSON array on GET /items
            let mut reader = BufReader::new(tcp);
            let mut req_line = String::new();
            if reader.read_line(&mut req_line).is_err() {
                continue;
            }
            let mut parts = req_line.split_ascii_whitespace();
            let method = parts.next().unwrap_or("").to_string();
            let path = parts.next().unwrap_or("").to_string();
            let mut content_len = 0usize;
            let mut headers = Vec::new();
            loop {
                let mut hline = String::new();
                if reader.read_line(&mut hline).is_err() {
                    break;
                }
                let tr = hline.trim_end_matches(['\r', '\n']);
                if tr.is_empty() {
                    break;
                }
                if let Some((k, v)) = tr.split_once(':') {
                    if k.trim().eq_ignore_ascii_case("content-length") {
                        content_len = v.trim().parse().unwrap_or(0);
                    }
                    headers.push((k.trim().to_string(), v.trim().to_string()));
                }
            }
            let mut body_buf = vec![0u8; content_len];
            if content_len > 0 && reader.read_exact(&mut body_buf).is_err() {
                continue;
            }
            let body = String::from_utf8_lossy(&body_buf).into_owned();
            if let Ok(mut g) = tcp_srv_log.lock() {
                g.push(CapturedHttpReq {
                    method: method.clone(),
                    path: path.clone(),
                    headers,
                    body,
                });
            }
            let (status, resp_body): (&str, &[u8]) = if method == "GET" && path == "/items" {
                ("200 OK", br#"[{"sku":"a1","qty":3},{"sku":"b2","qty":8}]"#)
            } else if method == "PUT" {
                ("204 No Content", b"")
            } else {
                ("200 OK", br#"{"ok":true}"#)
            };
            let mut w = reader.into_inner();
            let hdr = format!(
                "HTTP/1.1 {status}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                resp_body.len()
            );
            let _ = w.write_all(hdr.as_bytes());
            let _ = w.write_all(resp_body);
            let _ = w.flush();
        }
    });

    let tcp_src = r#"
module LiveLoopbackE2E

schema ItemRow
  sku: Text
  qty: Int
end

fn main(api: LocalHttpAllow(MoSvc), tok: Secret("mo_tok"), console: Console) : Int
  batch = table
    | sku  | qty |
    | "a1" | 3   |
  end
  _ = try api.post_json("/items", body: batch, headers: {"Authorization": "Bearer #{tok}"})
  _ = try api.put_json("/items/a1", body: "{\"qty\":4}")
  items_resp = try api.get_json("/items")
  (rows, bad) = items_resp.parse_table("", as: ItemRow)
  assert bad.empty?
  _ = try api.delete_json("/items/temp")
  console.print("ITEMS=#{rows.count()} SUM=#{rows.sum(.qty)}")
  0
end
"#;
    let mut local_http_bindings = HashMap::new();
    local_http_bindings.insert(
        "MoSvc".to_string(),
        format!("ready:{}", ready_path.display()),
    );
    let tcp_cfg = RunConfig {
        live_io: true,
        local_http_bindings,
        ..RunConfig::default()
    };
    let out = assert_oracle_vm_parity_with_cfg(tcp_src, &tcp_cfg)?;
    let _ = tcp_srv.join();
    assert_eq!(out, vec!["ITEMS=2 SUM=11"]);
    {
        let log = tcp_captured.lock().map_err(|e| format!("{e}"))?;
        assert_eq!(log.len(), 8);
        assert!(log[0].method == "POST" && log[0].body.contains("\"sku\":\"a1\""));
        assert!(
            log[0]
                .headers
                .iter()
                .any(|(k, v)| k == "Authorization" && v == "Bearer env:mo_tok")
        );
    }

    #[cfg(unix)]
    {
        use std::os::unix::net::UnixListener;

        let sock_path = tmp.path().join("admin.sock");
        let uds_listener = UnixListener::bind(&sock_path)?;
        let uds_hits = Arc::new(Mutex::new(Vec::new()));
        let uds_log = Arc::clone(&uds_hits);
        let uds_srv = thread::spawn(move || {
            for _ in 0..4 {
                let Ok((stream, _)) = uds_listener.accept() else {
                    break;
                };
                if let Some(req) = read_http_req_from_stream(
                    stream,
                    "200 OK",
                    "Content-Type: application/json\r\n",
                    br#"{"status":"healthy","workers":2}"#,
                ) && let Ok(mut g) = uds_log.lock()
                {
                    g.push(req);
                }
            }
        });

        let uds_src = r#"
module LiveUdsE2E
fn main(sock: LocalSocketAllow(MoAdmin), console: Console) : Int
  r1 = try sock.get_json("/admin/verify")
  r2 = try sock.delete_json("/admin/cache")
  st = r1.text_at("status")
  w = r1.int_at("workers")
  d = r2.int_at("workers")
  console.print("UDS=#{st} W=#{w} D=#{d}")
  0
end
"#;
        let mut local_socket_bindings = HashMap::new();
        local_socket_bindings.insert("MoAdmin".to_string(), sock_path.display().to_string());
        let uds_cfg = RunConfig {
            live_io: true,
            local_socket_bindings,
            ..RunConfig::default()
        };
        let uds_out = assert_oracle_vm_parity_with_cfg(uds_src, &uds_cfg)?;
        let _ = uds_srv.join();
        assert_eq!(uds_out, vec!["UDS=healthy W=2 D=2"]);
        assert_eq!(uds_hits.lock().map_err(|e| format!("{e}"))?.len(), 4);
    }

    Ok(())
}
