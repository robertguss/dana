#include "lexer.h"
#include "dana.tab.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *read_all(const char *path, size_t *out_len) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        perror(path);
        return NULL;
    }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    if (sz < 0) {
        fclose(f);
        return NULL;
    }
    fseek(f, 0, SEEK_SET);
    char *buf = malloc((size_t)sz + 1);
    if (!buf) {
        fclose(f);
        return NULL;
    }
    size_t n = fread(buf, 1, (size_t)sz, f);
    buf[n] = '\0';
    fclose(f);
    *out_len = n;
    return buf;
}

int main(int argc, char **argv) {
    int start_token = START_FILE;
    const char *path = NULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--fragment") == 0) {
            start_token = START_FRAGMENT;
        } else if (!path) {
            path = argv[i];
        } else {
            fprintf(stderr, "usage: dana-grammar [--fragment] FILE\n");
            return 2;
        }
    }
    if (!path) {
        fprintf(stderr, "usage: dana-grammar [--fragment] FILE\n");
        return 2;
    }

    size_t len = 0;
    char *src = read_all(path, &len);
    if (!src) return 2;

    Lexer lx;
    lexer_init(&lx, path, src, len, start_token);
    int rc = yyparse(&lx);
    free(src);

    if (rc != 0 || lx.has_error) {
        fprintf(stderr, "%s:%d:%d: %s\n", path, lx.err_line, lx.err_col,
                lx.has_error ? lx.err_msg : "syntax error");
        return 1;
    }
    return 0;
}
