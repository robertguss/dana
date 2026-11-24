/-
  Main.lean
  `danacore` CLI oracle executable for Dana Core IR v0.1.

  Usage:
    danacore <file.core> [--fuel N] [--allow-export tag1,tag2]
    danacore run <file.core> [--fuel N] [--allow-export tag1,tag2]
    danacore check <file.core>
    danacore fmt <file.core>
-/
import DanaCore.Syntax
import DanaCore.Check
import DanaCore.Eval
import DanaCore.Text

open DanaCore

structure CliOpts where
  mode           : String := "run"
  modeSet        : Bool := false
  path           : Option String := none
  fuel           : Nat := 4096
  fuelSet        : Bool := false
  allowExport    : TagSet := TagSet.empty
  allowExportSet : Bool := false

def isTagStartChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

def isTagIdentChar (c : Char) : Bool :=
  isTagStartChar c || ('0' ≤ c && c ≤ '9') || c == '-'

def parseAsciiNat (raw : String) : Option Nat :=
  if raw.isEmpty || !raw.toList.all (fun c => '0' ≤ c && c ≤ '9') then none
  else raw.toNat?

def parseCommaTags (raw : String) : Except String TagSet := do
  if raw.isEmpty then
    .error "empty tag list for --allow-export"
  else if raw.startsWith "--" then
    .error s!"missing argument for --allow-export (got flag '{raw}')"
  else
    let parts := raw.splitOn ","
    let mut seen : List String := []
    for part in parts do
      match part.toList with
      | [] => throw s!"invalid tag '{part}' in --allow-export"
      | c :: cs =>
        if !isTagStartChar c || !cs.all isTagIdentChar then
          throw s!"invalid tag '{part}' in --allow-export"
      if seen.contains part then
        throw s!"duplicate tag '{part}' in --allow-export"
      seen := part :: seen
    .ok (TagSet.ofList parts)

def parseCliArgs : List String → CliOpts → Except String CliOpts
  | [], opts =>
    if opts.path.isSome then .ok opts
    else .error "usage: danacore [run|check|fmt] <file.core> [--fuel <N>] [--allow-export <tags>]"
  | "run" :: rest, opts =>
    if !opts.modeSet && opts.path.isNone then
      parseCliArgs rest { opts with mode := "run", modeSet := true }
    else .error "unexpected positional argument 'run'"
  | "check" :: rest, opts =>
    if !opts.modeSet && opts.path.isNone then
      parseCliArgs rest { opts with mode := "check", modeSet := true }
    else .error "unexpected positional argument 'check'"
  | "fmt" :: rest, opts =>
    if !opts.modeSet && opts.path.isNone then
      parseCliArgs rest { opts with mode := "fmt", modeSet := true }
    else .error "unexpected positional argument 'fmt'"
  | ["--fuel"], _ =>
    .error "missing argument for --fuel"
  | "--fuel" :: nStr :: rest, opts =>
    if opts.fuelSet then
      .error "duplicate --fuel flag"
    else if nStr.startsWith "--" then
      .error s!"missing argument for --fuel (got flag '{nStr}')"
    else
      match parseAsciiNat nStr with
      | some n => parseCliArgs rest { opts with fuel := n, fuelSet := true }
      | none => .error s!"invalid --fuel integer '{nStr}'"
  | ["--allow-export"], _ =>
    .error "missing argument for --allow-export"
  | "--allow-export" :: tStr :: rest, opts =>
    if opts.allowExportSet then
      .error "duplicate --allow-export flag"
    else do
      let tags ← parseCommaTags tStr
      parseCliArgs rest { opts with allowExport := tags, allowExportSet := true }
  | arg :: rest, opts =>
    if arg.startsWith "--" then
      .error s!"unknown flag '{arg}'"
    else if opts.path.isNone then
      parseCliArgs rest { opts with path := some arg }
    else
      .error s!"unexpected positional argument '{arg}'"

def main (args : List String) : IO UInt32 := do
  match parseCliArgs args {} with
  | .error msg =>
    IO.eprintln s!"danacore error: {msg}"
    return 2
  | .ok opts =>
    let filePath := opts.path.getD ""
    let wire ←
      try
        IO.FS.readFile filePath
      catch e =>
        IO.eprintln s!"danacore io error: {e}"
        return 2
    match parseProgram wire with
    | .error parseErr =>
      IO.eprintln s!"danacore parse error: {parseErr}"
      return 1
    | .ok prog =>
      if opts.mode == "fmt" then
        IO.print (printProgram prog)
        return 0
      match checkProgram prog with
      | .error checkErr =>
        IO.eprintln s!"danacore check error: {checkErr}"
        return 1
      | .ok () =>
        if opts.mode == "check" then
          IO.println "ok"
          return 0
        let initWorld : World := { runtimeAllowExport := opts.allowExport }
        match runProgram opts.fuel prog initWorld with
        | .error runErr =>
          IO.eprintln s!"danacore runtime error: {runErr}"
          return 1
        | .ok report =>
          IO.print (printReport report)
          match report.status with
          | .ok => return 0
          | .stopped | .failed => return 1
