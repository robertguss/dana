CC ?= gcc
BISON ?= bison
CFLAGS ?= -std=c17 -Wall -Wextra -Werror -O2

.PHONY: grammar formal oracle check-all clean

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

check-all: grammar formal oracle

clean:
	rm -rf build
