CC ?= gcc
BISON ?= bison
CFLAGS ?= -std=c17 -Wall -Wextra -Werror -O2

.PHONY: grammar formal oracle test-parser-parity test-examples test-db test-phase4 test-v04 test-v05 test-v06 test-diff fuzz-parsers fuzz-soak soak learnability bench keel-qa check-all check-v03 check-v04 check-v05 check-v06 clean

build/dana.tab.c build/dana.tab.h: grammar/dana.y
	mkdir -p build
	$(BISON) -Werror -Wconflicts-sr -Wconflicts-rr --defines=build/dana.tab.h -o build/dana.tab.c grammar/dana.y

build/dana.tab.o: build/dana.tab.c build/dana.tab.h grammar/lexer.h
	$(CC) $(CFLAGS) -Wno-unused-but-set-variable -Ibuild -Igrammar -c build/dana.tab.c -o build/dana.tab.o

build/dana-grammar: build/dana.tab.o build/dana.tab.h grammar/lexer.c grammar/lexer.h grammar/main.c
	$(CC) $(CFLAGS) -Ibuild -Igrammar build/dana.tab.o grammar/lexer.c grammar/main.c -o build/dana-grammar

grammar: build/dana-grammar
	python3 grammar/check.py

formal:
	export PATH="$$HOME/.elan/bin:/opt/elan/bin:$$PATH" && cd formal && lake build DanaCore danacore
	@tmp=$$(mktemp) && \
	printf '(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl "main" fn false (("c" (lty (console (tags)) (tags)))) (tags) (lty (unit) (tags)) (host console-print ((var "c") (lit (lit-text "hello-dana")))))) (some "main") (meta))\n' > "$$tmp" && \
	check_out=$$(./formal/.lake/build/bin/danacore check "$$tmp") && \
	test "$$check_out" = "ok" && \
	run_out=$$(./formal/.lake/build/bin/danacore run "$$tmp") && \
	test "$$run_out" = '(dana-report 0.1 (status ok) (diagnostic (none)) (stdout "hello-dana") (stderr) (written-files) (written-tables) (fake-consoles) (fake-files))' && \
	fmt_out=$$(./formal/.lake/build/bin/danacore fmt "$$tmp") && \
	printf '%s\n' "$$fmt_out" | diff -u "$$tmp" - && \
	! ./formal/.lake/build/bin/danacore "$$tmp" check >/dev/null 2>&1 && \
	! ./formal/.lake/build/bin/danacore run "$$tmp" --fuel 10 --fuel 20 >/dev/null 2>&1 && \
	! ./formal/.lake/build/bin/danacore run "$$tmp" --allow-export pii --allow-export ferpa >/dev/null 2>&1 && \
	! ./formal/.lake/build/bin/danacore run "$$tmp" --allow-export --fuel >/dev/null 2>&1 && \
	! ./formal/.lake/build/bin/danacore run "$$tmp" --fuel 1_0 >/dev/null 2>&1 && \
	! ./formal/.lake/build/bin/danacore run "$$tmp" --allow-export pii,,ferpa >/dev/null 2>&1 && \
	! ./formal/.lake/build/bin/danacore run "$$tmp" --allow-export -pii >/dev/null 2>&1 && \
	rm -f "$$tmp" && \
	echo "danacore CLI smoke checks passed."

oracle:
	cargo fmt --all -- --check
	cargo clippy --all-targets -- -D warnings
	RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
	cargo test --all-targets

test-parser-parity:
	cargo test --test parser_parity

test-examples:
	cargo test --test examples_e2e

test-db:
	cargo test --test db_drivers --test db_e2e

test-phase4:
	cargo test --test phase4a_formats_https --test phase4b_stats_viz --test phase4c_repl_vendor_e2e

test-v04:
	cargo test --test v04_columnar_io

test-v05:
	cargo test --test v05_wts_readiness

test-v06:
	cargo test --test v06_dogfood_fixes

test-diff:
	cargo test --test differential_vm --test differential_sql --test differential_lean

fuzz-parsers:
	cargo test --release --test fuzz_parsers -- --nocapture

fuzz-soak:
	cargo test --release --test hardening_soak_privacy -- --nocapture

soak:
	DANA_SOAK_CASES=10000 cargo test --release --test hardening_soak_privacy -- --nocapture

learnability:
	cargo test --test learnability_harness -- --nocapture

bench:
	cargo build --release && python3 benchmarks/run_benchmarks.py

keel-qa:
	./scripts/keel-qa/run.sh

check-all: grammar formal oracle

check-v03: grammar formal oracle fuzz-parsers fuzz-soak learnability

check-v04: grammar formal oracle fuzz-parsers fuzz-soak learnability

check-v05: grammar formal oracle fuzz-parsers fuzz-soak learnability

check-v06: grammar formal oracle fuzz-parsers fuzz-soak learnability

clean:
	rm -rf build
