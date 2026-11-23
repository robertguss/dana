CC ?= gcc
BISON ?= bison
CFLAGS ?= -std=c17 -Wall -Wextra -Werror -O2

.PHONY: grammar clean

build/dana.tab.c build/dana.tab.h: grammar/dana.y
	mkdir -p build
	$(BISON) -Werror -Wconflicts-sr -Wconflicts-rr --defines=build/dana.tab.h -o build/dana.tab.c grammar/dana.y

build/dana.tab.o: build/dana.tab.c build/dana.tab.h grammar/lexer.h
	$(CC) $(CFLAGS) -Wno-unused-but-set-variable -Ibuild -Igrammar -c build/dana.tab.c -o build/dana.tab.o

build/dana-grammar: build/dana.tab.o build/dana.tab.h grammar/lexer.c grammar/lexer.h grammar/main.c
	$(CC) $(CFLAGS) -Ibuild -Igrammar build/dana.tab.o grammar/lexer.c grammar/main.c -o build/dana-grammar

grammar: build/dana-grammar
	python3 grammar/check.py

clean:
	rm -rf build
