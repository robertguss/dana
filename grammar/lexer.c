#include "lexer.h"
#include "dana.tab.h"

#include <ctype.h>
#include <stdio.h>
#include <string.h>

static void set_err(Lexer *lx, int line, int col, const char *msg) {
    if (!lx->has_error) {
        lx->has_error = true;
        lx->err_line = line;
        lx->err_col = col;
        snprintf(lx->err_msg, sizeof(lx->err_msg), "%s", msg);
    }
}

/* Validate UTF-8 and reject invisible formatting / control characters (Reference 2.1). */
static bool validate_utf8_and_chars(Lexer *lx) {
    size_t i = 0;
    int line = 1;
    int col = 1;
    while (i < lx->len) {
        unsigned char b = (unsigned char)lx->src[i];
        unsigned int cp = 0;
        size_t adv = 1;

        if (b < 0x80) {
            cp = b;
            adv = 1;
        } else if ((b & 0xE0) == 0xC0) {
            if (i + 1 >= lx->len) { set_err(lx, line, col, "invalid UTF-8"); return false; }
            unsigned char b1 = (unsigned char)lx->src[i + 1];
            if ((b1 & 0xC0) != 0x80) { set_err(lx, line, col, "invalid UTF-8"); return false; }
            cp = ((unsigned int)(b & 0x1F) << 6) | (b1 & 0x3F);
            if (cp < 0x80) { set_err(lx, line, col, "overlong UTF-8"); return false; }
            adv = 2;
        } else if ((b & 0xF0) == 0xE0) {
            if (i + 2 >= lx->len) { set_err(lx, line, col, "invalid UTF-8"); return false; }
            unsigned char b1 = (unsigned char)lx->src[i + 1];
            unsigned char b2 = (unsigned char)lx->src[i + 2];
            if ((b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80) {
                set_err(lx, line, col, "invalid UTF-8"); return false;
            }
            cp = ((unsigned int)(b & 0x0F) << 12) | ((unsigned int)(b1 & 0x3F) << 6) | (b2 & 0x3F);
            if (cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF)) {
                set_err(lx, line, col, "invalid UTF-8 scalar"); return false;
            }
            adv = 3;
        } else if ((b & 0xF8) == 0xF0) {
            if (i + 3 >= lx->len) { set_err(lx, line, col, "invalid UTF-8"); return false; }
            unsigned char b1 = (unsigned char)lx->src[i + 1];
            unsigned char b2 = (unsigned char)lx->src[i + 2];
            unsigned char b3 = (unsigned char)lx->src[i + 3];
            if ((b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 || (b3 & 0xC0) != 0x80) {
                set_err(lx, line, col, "invalid UTF-8"); return false;
            }
            cp = ((unsigned int)(b & 0x07) << 18) | ((unsigned int)(b1 & 0x3F) << 12)
               | ((unsigned int)(b2 & 0x3F) << 6) | (b3 & 0x3F);
            if (cp < 0x10000 || cp > 0x10FFFF) {
                set_err(lx, line, col, "invalid UTF-8 scalar"); return false;
            }
            adv = 4;
        } else {
            set_err(lx, line, col, "invalid UTF-8 byte");
            return false;
        }

        /* Reject ASCII controls except \t, \n, \r, and invisible bidi/zero-width chars. */
        if ((cp < 0x20 && cp != '\t' && cp != '\n' && cp != '\r') || cp == 0x7F
            || (cp >= 0x200B && cp <= 0x200F)
            || (cp >= 0x202A && cp <= 0x202E)
            || (cp >= 0x2066 && cp <= 0x2069)
            || cp == 0xFEFF) {
            set_err(lx, line, col, "forbidden invisible or control character in source");
            return false;
        }

        if (cp == '\n') {
            line++;
            col = 1;
        } else {
            col++;
        }
        i += adv;
    }
    return true;
}

void lexer_init(Lexer *lx, const char *filename, const char *src, size_t len, int start_token) {
    memset(lx, 0, sizeof(*lx));
    lx->filename = filename;
    lx->src = src;
    lx->len = len;
    lx->line = 1;
    lx->col = 1;
    lx->start_token = start_token;
    validate_utf8_and_chars(lx);
}

static char peek_at(const Lexer *lx, size_t offset) {
    if (lx->pos + offset >= lx->len) return '\0';
    return lx->src[lx->pos + offset];
}

static char advance(Lexer *lx) {
    if (lx->pos >= lx->len) return '\0';
    char c = lx->src[lx->pos++];
    if (c == '\n') {
        lx->line++;
        lx->col = 1;
    } else {
        lx->col++;
    }
    return c;
}

static bool token_continues_after(int tok) {
    switch (tok) {
        case 0:
        case NL:
        case LPAREN: case LBRACK: case LBRACE:
        case COMMA: case DOT: case ASSIGN: case PIPE:
        case AND: case OR: case NOT: case IS: case QQ:
        case EQ: case NE: case LT: case LE: case GT: case GE:
        case PLUS: case MINUS: case STAR: case SLASH: case PERCENT:
            return true;
        default:
            return false;
    }
}

static bool is_ident_start(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

static bool is_ident_cont(char c) {
    return is_ident_start(c) || (c >= '0' && c <= '9');
}

/* Peek ahead past horizontal whitespace and comments to see if the next non-blank line
 * begins with a token that continues the previous line (., |>, else, binary op except -). */
static bool next_line_continues(const Lexer *lx) {
    size_t p = lx->pos;
    while (p < lx->len) {
        char c = lx->src[p];
        if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
            p++;
            continue;
        }
        if (c == '#') {
            while (p < lx->len && lx->src[p] != '\n') p++;
            continue;
        }
        break;
    }
    if (p >= lx->len) return false;

    char c = lx->src[p];
    char c2 = (p + 1 < lx->len) ? lx->src[p + 1] : '\0';
    if (c == '.' || c == ')' || c == ']' || c == '}') return true;
    if (c == '|' && c2 == '>') return true;
    if (c == '+' || c == '*' || c == '/' || c == '%') return true;
    if (c == '?' && c2 == '?') return true;
    if ((c == '=' && c2 == '=') || (c == '!' && c2 == '=')
        || c == '<' || c == '>') return true;

    /* `and`, `or`, `is` at start of next line continue the previous expression. */
    if (strncmp(lx->src + p, "and", 3) == 0 && (p + 3 >= lx->len || !is_ident_cont(lx->src[p + 3])))
        return true;
    if (strncmp(lx->src + p, "or", 2) == 0 && (p + 2 >= lx->len || !is_ident_cont(lx->src[p + 2])))
        return true;
    if (strncmp(lx->src + p, "is", 2) == 0 && (p + 2 >= lx->len || !is_ident_cont(lx->src[p + 2])))
        return true;

    return false;
}

static int lookup_keyword(const char *s, size_t n) {
    struct { const char *kw; int tok; } table[] = {
        {"and", AND}, {"assert", ASSERT}, {"break", BREAK}, {"case", CASE},
        {"const", CONST}, {"continue", CONTINUE}, {"else", ELSE}, {"end", END},
        {"enum", ENUM}, {"examples", EXAMPLES}, {"expose", EXPOSE}, {"false", FALSE},
        {"fn", FN}, {"for", FOR}, {"if", IF}, {"in", IN}, {"is", IS},
        {"module", MODULE}, {"none", NONE}, {"not", NOT}, {"or", OR},
        {"promise", PROMISE}, {"return", RETURN}, {"schema", SCHEMA}, {"stop", STOP},
        {"struct", STRUCT}, {"table", TABLE}, {"tag", TAG}, {"test", TEST},
        {"true", TRUE}, {"try", TRY}, {"use", USE}, {"var", VAR},
        {"where", WHERE}, {"while", WHILE},
    };
    for (size_t i = 0; i < sizeof(table) / sizeof(table[0]); i++) {
        if (strlen(table[i].kw) == n && memcmp(s, table[i].kw, n) == 0) {
            return table[i].tok;
        }
    }
    return 0;
}

static bool is_4d_2d_2d(const Lexer *lx, size_t p) {
    if (p + 10 > lx->len) return false;
    return isdigit((unsigned char)lx->src[p])
        && isdigit((unsigned char)lx->src[p + 1])
        && isdigit((unsigned char)lx->src[p + 2])
        && isdigit((unsigned char)lx->src[p + 3])
        && lx->src[p + 4] == '-'
        && isdigit((unsigned char)lx->src[p + 5])
        && isdigit((unsigned char)lx->src[p + 6])
        && lx->src[p + 7] == '-'
        && isdigit((unsigned char)lx->src[p + 8])
        && isdigit((unsigned char)lx->src[p + 9]);
}

static int lex_string(Lexer *lx, bool multiline, bool resuming) {
    while (lx->pos < lx->len) {
        char c = peek_at(lx, 0);
        if (multiline) {
            if (c == '"' && peek_at(lx, 1) == '"' && peek_at(lx, 2) == '"') {
                advance(lx); advance(lx); advance(lx);
                return resuming ? TEXT_TAIL : TEXT;
            }
        } else {
            if (c == '"') {
                advance(lx);
                return resuming ? TEXT_TAIL : TEXT;
            }
            if (c == '\n') {
                set_err(lx, lx->line, lx->col, "unterminated string literal");
                return YYerror;
            }
        }

        if (c == '\\') {
            advance(lx);
            if (lx->pos >= lx->len) {
                set_err(lx, lx->line, lx->col, "unterminated string escape");
                return YYerror;
            }
            advance(lx);
            continue;
        }

        if (c == '#' && peek_at(lx, 1) == '{') {
            advance(lx); advance(lx);
            if (lx->interp_top >= 64) {
                set_err(lx, lx->line, lx->col, "interpolation nesting too deep");
                return YYerror;
            }
            lx->interp_stack[lx->interp_top] = lx->paren_depth;
            lx->interp_multiline[lx->interp_top] = multiline;
            lx->interp_top++;
            lx->paren_depth++;
            return resuming ? TEXT_MID : TEXT_HEAD;
        }

        advance(lx);
    }
    set_err(lx, lx->line, lx->col, "unterminated string literal");
    return YYerror;
}

static int emit(Lexer *lx, int tok, DanaLoc *loc, int sl, int sc) {
    loc->first_line = sl;
    loc->first_column = sc;
    loc->last_line = lx->line;
    loc->last_column = lx->col;
    lx->prev_token = tok;
    return tok;
}

int dana_lex(void *yylval, DanaLoc *loc, Lexer *lx) {
    (void)yylval;

    if (lx->has_error) {
        loc->first_line = lx->err_line;
        loc->first_column = lx->err_col;
        loc->last_line = lx->err_line;
        loc->last_column = lx->err_col;
        return YYerror;
    }

    if (!lx->sent_start) {
        lx->sent_start = true;
        loc->first_line = 1;
        loc->first_column = 1;
        loc->last_line = 1;
        loc->last_column = 1;
        return lx->start_token;
    }

    for (;;) {
        bool saw_space = false;
        bool saw_nl = false;
        int nl_line = lx->line;
        int nl_col = lx->col;

        while (lx->pos < lx->len) {
            char c = peek_at(lx, 0);
            if (c == ' ' || c == '\t' || c == '\r') {
                saw_space = true;
                advance(lx);
            } else if (c == '#') {
                while (lx->pos < lx->len && peek_at(lx, 0) != '\n') advance(lx);
            } else if (c == '\n') {
                if (!saw_nl) {
                    nl_line = lx->line;
                    nl_col = lx->col;
                }
                saw_nl = true;
                saw_space = true;
                advance(lx);
            } else {
                break;
            }
        }

        if (saw_nl && lx->paren_depth == 0 && !token_continues_after(lx->prev_token)) {
            if (!next_line_continues(lx)) {
                return emit(lx, NL, loc, nl_line, nl_col);
            }
        }

        if (lx->pos >= lx->len) {
            if (lx->prev_token != 0 && lx->prev_token != NL && lx->paren_depth == 0) {
                return emit(lx, NL, loc, lx->line, lx->col);
            }
            loc->first_line = lx->line;
            loc->first_column = lx->col;
            loc->last_line = lx->line;
            loc->last_column = lx->col;
            return 0;
        }

        int sl = lx->line;
        int sc = lx->col;
        char c = peek_at(lx, 0);
        char c2 = peek_at(lx, 1);

        /* Resume string interpolation on matching '}'. */
        if (c == '}' && lx->interp_top > 0
            && lx->paren_depth == lx->interp_stack[lx->interp_top - 1] + 1) {
            advance(lx);
            lx->interp_top--;
            lx->paren_depth = lx->interp_stack[lx->interp_top];
            bool multi = lx->interp_multiline[lx->interp_top];
            int tok = lex_string(lx, multi, true);
            return emit(lx, tok, loc, sl, sc);
        }

        /* Strings (single-line and multiline """). */
        if (c == '"') {
            if (c2 == '"' && peek_at(lx, 2) == '"') {
                advance(lx); advance(lx); advance(lx);
                int tok = lex_string(lx, true, false);
                return emit(lx, tok, loc, sl, sc);
            }
            advance(lx);
            int tok = lex_string(lx, false, false);
            return emit(lx, tok, loc, sl, sc);
        }

        /* Numbers, ISO Dates (YYYY-MM-DD), and ISO Timestamps (YYYY-MM-DDTHH:MM:SSZ). */
        if (isdigit((unsigned char)c)) {
            if (is_4d_2d_2d(lx, lx->pos)) {
                for (int k = 0; k < 10; k++) advance(lx);
                if (peek_at(lx, 0) == 'T') {
                    advance(lx);
                    while (lx->pos < lx->len) {
                        char tc = peek_at(lx, 0);
                        if (isdigit((unsigned char)tc) || tc == ':' || tc == '.'
                            || tc == 'Z' || tc == '+' || tc == '-') {
                            advance(lx);
                        } else {
                            break;
                        }
                    }
                    return emit(lx, TIMESTAMP, loc, sl, sc);
                }
                return emit(lx, DATE, loc, sl, sc);
            }

            while (isdigit((unsigned char)peek_at(lx, 0)) || peek_at(lx, 0) == '_') advance(lx);
            bool is_dec = false;
            if (peek_at(lx, 0) == '.' && isdigit((unsigned char)peek_at(lx, 1))) {
                is_dec = true;
                advance(lx);
                while (isdigit((unsigned char)peek_at(lx, 0)) || peek_at(lx, 0) == '_') advance(lx);
            }
            if ((peek_at(lx, 0) == 'e' || peek_at(lx, 0) == 'E')
                && (isdigit((unsigned char)peek_at(lx, 1))
                    || ((peek_at(lx, 1) == '+' || peek_at(lx, 1) == '-')
                        && isdigit((unsigned char)peek_at(lx, 2))))) {
                is_dec = true;
                advance(lx);
                if (peek_at(lx, 0) == '+' || peek_at(lx, 0) == '-') advance(lx);
                while (isdigit((unsigned char)peek_at(lx, 0))) advance(lx);
            }
            return emit(lx, is_dec ? DECIMAL : INT, loc, sl, sc);
        }

        /* Atoms (:month, :pearson) vs ':'. */
        if (c == ':' && (c2 >= 'a' && c2 <= 'z')
            && (saw_space || lx->prev_token == 0 || lx->prev_token == NL
                || lx->prev_token == LPAREN || lx->prev_token == LBRACK
                || lx->prev_token == LBRACE || lx->prev_token == COMMA
                || lx->prev_token == COLON || lx->prev_token == ASSIGN
                || lx->prev_token == PIPE || lx->prev_token == BAR)) {
            advance(lx);
            while (is_ident_cont(peek_at(lx, 0))) advance(lx);
            return emit(lx, ATOM, loc, sl, sc);
        }

        /* Identifiers, CapNames, Keywords, and `_`. */
        if (is_ident_start(c)) {
            size_t start = lx->pos;
            while (is_ident_cont(peek_at(lx, 0))) advance(lx);
            size_t n = lx->pos - start;
            if (n == 1 && lx->src[start] == '_') {
                return emit(lx, UNDERSCORE, loc, sl, sc);
            }
            /* Optional trailing '?' (boolean predicate) or '!' (asserting unwrap) on lowercase names. */
            bool has_suffix = false;
            if (lx->src[start] >= 'a' && lx->src[start] <= 'z') {
                char suf = peek_at(lx, 0);
                if (suf == '?' && peek_at(lx, 1) != '?') {
                    advance(lx);
                    has_suffix = true;
                } else if (suf == '!' && peek_at(lx, 1) != '=') {
                    advance(lx);
                    has_suffix = true;
                }
            }
            if (!has_suffix) {
                int kw = lookup_keyword(lx->src + start, n);
                if (kw != 0) {
                    return emit(lx, kw, loc, sl, sc);
                }
            }
            if (lx->src[start] >= 'A' && lx->src[start] <= 'Z') {
                return emit(lx, CAPNAME, loc, sl, sc);
            }
            return emit(lx, NAME, loc, sl, sc);
        }

        /* Multi-character operators & punctuation. */
        if (c == '|' && c2 == '>') { advance(lx); advance(lx); return emit(lx, PIPE, loc, sl, sc); }
        if (c == '?' && c2 == '?') { advance(lx); advance(lx); return emit(lx, QQ, loc, sl, sc); }
        if (c == '.' && c2 == '.') { advance(lx); advance(lx); return emit(lx, DOTDOT, loc, sl, sc); }
        if (c == '=' && c2 == '=') { advance(lx); advance(lx); return emit(lx, EQ, loc, sl, sc); }
        if (c == '!' && c2 == '=') { advance(lx); advance(lx); return emit(lx, NE, loc, sl, sc); }
        if (c == '<' && c2 == '=') { advance(lx); advance(lx); return emit(lx, LE, loc, sl, sc); }
        if (c == '>' && c2 == '=') { advance(lx); advance(lx); return emit(lx, GE, loc, sl, sc); }

        /* Single-character delimiters & operators. */
        advance(lx);
        switch (c) {
            case '(': lx->paren_depth++; return emit(lx, LPAREN, loc, sl, sc);
            case ')': if (lx->paren_depth > 0) lx->paren_depth--; return emit(lx, RPAREN, loc, sl, sc);
            case '[': lx->paren_depth++; return emit(lx, LBRACK, loc, sl, sc);
            case ']': if (lx->paren_depth > 0) lx->paren_depth--; return emit(lx, RBRACK, loc, sl, sc);
            case '{': lx->paren_depth++; return emit(lx, LBRACE, loc, sl, sc);
            case '}': if (lx->paren_depth > 0) lx->paren_depth--; return emit(lx, RBRACE, loc, sl, sc);
            case ',': return emit(lx, COMMA, loc, sl, sc);
            case ':': return emit(lx, COLON, loc, sl, sc);
            case '.': return emit(lx, DOT, loc, sl, sc);
            case '|': return emit(lx, BAR, loc, sl, sc);
            case '?': return emit(lx, QMARK, loc, sl, sc);
            case '=': return emit(lx, ASSIGN, loc, sl, sc);
            case '<': return emit(lx, LT, loc, sl, sc);
            case '>': return emit(lx, GT, loc, sl, sc);
            case '+': return emit(lx, PLUS, loc, sl, sc);
            case '-': return emit(lx, MINUS, loc, sl, sc);
            case '*': return emit(lx, STAR, loc, sl, sc);
            case '/': return emit(lx, SLASH, loc, sl, sc);
            case '%': return emit(lx, PERCENT, loc, sl, sc);
            default: {
                char msg[64];
                snprintf(msg, sizeof(msg), "unexpected character '%c'", c);
                set_err(lx, sl, sc, msg);
                return YYerror;
            }
        }
    }
}
