#ifndef DANA_LEXER_H
#define DANA_LEXER_H

#include <stddef.h>
#include <stdbool.h>

typedef struct DanaLoc {
    int first_line;
    int first_column;
    int last_line;
    int last_column;
} DanaLoc;

#define YYLTYPE DanaLoc

typedef struct Lexer {
    const char *filename;
    const char *src;
    size_t len;
    size_t pos;
    int line;
    int col;

    /* Start mode token injected first (START_FILE or START_FRAGMENT). */
    int start_token;
    bool sent_start;

    /* Delimiter nesting depth for suppressing NL inside (), [], {}. */
    int paren_depth;
    /* Stack of brace depths for string interpolation #{...}. */
    int interp_stack[64];
    int interp_top;
    bool interp_multiline[64];

    /* Last emitted significant token for line-continuation & atom disambiguation. */
    int prev_token;
    bool prev_was_space;
    bool pending_nl;
    bool at_eof;

    /* Inside a Markdown `table ... end` block, newlines end rows cleanly. */
    int table_depth;

    /* Error state. */
    bool has_error;
    int err_line;
    int err_col;
    char err_msg[256];
} Lexer;

void lexer_init(Lexer *lx, const char *filename, const char *src, size_t len, int start_token);
int dana_lex(void *yylval, DanaLoc *loc, Lexer *lx);

#endif
