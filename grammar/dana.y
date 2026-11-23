/* The executable grammar of Dana, Language Reference v0.1.
 *
 * Bison builds an IELR(1) parser with ZERO conflicts (%expect 0) and ZERO
 * operator precedence declarations: every precedence level is explicit.
 */

%code top {
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
}

%code requires {
#include "lexer.h"
}

%code provides {
int yylex(void *value, DanaLoc *location, Lexer *lx);
}

%code {
int yylex(void *value, DanaLoc *location, Lexer *lx) {
    return dana_lex(value, location, lx);
}

static void yyerror(DanaLoc *location, Lexer *lx, const char *message) {
    if (!lx->has_error) {
        lx->has_error = true;
        lx->err_line = location->first_line;
        lx->err_col = location->first_column;
        snprintf(lx->err_msg, sizeof(lx->err_msg), "%s", message);
    }
}
}

%define api.pure full
%define api.value.type {int}
%define parse.error detailed
%define lr.type ielr
%locations
%param {Lexer *lx}
%expect 0

%token START_FILE START_FRAGMENT
%token NL "end of line"
%token NAME "name" CAPNAME "capitalized name" UNDERSCORE "_"
%token ATOM "atom"
%token INT "whole number" DECIMAL "decimal number" DATE "date literal" TIMESTAMP "timestamp literal"
%token TEXT "text"
%token TEXT_HEAD "text before #{" TEXT_MID "text between interpolations" TEXT_TAIL "text after }"

%token MODULE "module" EXPOSE "expose" USE "use" TAG "tag"
%token SCHEMA "schema" STRUCT "struct" ENUM "enum" CONST "const"
%token FN "fn" VAR "var" IF "if" ELSE "else" CASE "case"
%token FOR "for" IN "in" WHILE "while"
%token BREAK "break" CONTINUE "continue" RETURN "return" TRY "try"
%token AND "and" OR "or" NOT "not" IS "is"
%token TRUE "true" FALSE "false" NONE "none"
%token STOP "stop" PROMISE "promise" EXAMPLES "examples" TEST "test" ASSERT "assert"
%token TABLE "table" WHERE "where" END "end"

%token LPAREN "(" RPAREN ")" LBRACK "[" RBRACK "]" LBRACE "{" RBRACE "}"
%token COMMA "," COLON ":" DOT "." DOTDOT ".." BAR "|"
%token PIPE "|>" QMARK "?" QQ "??"
%token ASSIGN "="
%token EQ "==" NE "!=" LT "<" LE "<=" GT ">" GE ">="
%token PLUS "+" MINUS "-" STAR "*" SLASH "/" PERCENT "%"

%start start

%%

start
    : START_FILE file
    | START_FRAGMENT fragment
    ;

/* Files and Fragments */

file
    : opt_nls module_header top_items
    ;

fragment
    : opt_nls fragment_items
    | opt_nls module_header fragment_items
    ;

opt_nls
    : %empty
    | opt_nls NL
    ;

/* Identifiers */

ident
    : NAME
    | WHERE
    | TAG
    ;

member_name
    : NAME
    | CAPNAME
    | WHERE
    | TAG
    | TABLE
    ;

/* Module Header */

module_header
    : MODULE module_path NL opt_nls expose uses
    ;

module_path
    : CAPNAME
    | module_path DOT CAPNAME
    ;

expose
    : %empty
    | EXPOSE expose_items NL opt_nls
    ;

expose_items
    : expose_item
    | expose_items COMMA expose_item
    ;

expose_item
    : ident
    | CAPNAME
    | CAPNAME LPAREN DOTDOT RPAREN
    ;

uses
    : %empty
    | uses use_decl
    ;

use_decl
    : USE module_path NL opt_nls
    | USE module_path LBRACE use_items RBRACE NL opt_nls
    ;

use_items
    : use_item
    | use_items COMMA use_item
    ;

use_item
    : ident
    | CAPNAME
    ;

/* Top-level Items */

top_items
    : %empty
    | top_items top_item
    ;

top_item
    : tag_decl
    | schema_decl
    | struct_decl
    | enum_decl
    | const_decl
    | fn_decl
    | test_decl
    ;

fragment_items
    : %empty
    | fragment_items fragment_item
    ;

fragment_item
    : tag_decl
    | schema_decl
    | struct_decl
    | enum_decl
    | const_decl
    | fn_decl
    | test_decl
    | stmt
    ;

/* Declarations */

tag_decl
    : TAG ident NL opt_nls
    ;

schema_decl
    : SCHEMA CAPNAME opt_tags NL opt_nls schema_fields END NL opt_nls
    ;

schema_fields
    : %empty
    | schema_fields schema_field
    ;

schema_field
    : ident COLON type_expr opt_tags opt_where NL opt_nls
    ;

opt_tags
    : %empty
    | LBRACK tag_list RBRACK
    ;

tag_list
    : %empty
    | tag_items
    ;

tag_items
    : ident
    | tag_items COMMA ident
    ;

opt_where
    : %empty
    | WHERE expr
    ;

struct_decl
    : STRUCT CAPNAME NL opt_nls struct_fields END NL opt_nls
    ;

struct_fields
    : %empty
    | struct_fields struct_field
    ;

struct_field
    : ident COLON type_expr opt_tags NL opt_nls
    ;

enum_decl
    : ENUM CAPNAME NL opt_nls enum_variants END NL opt_nls
    ;

enum_variants
    : %empty
    | enum_variants enum_variant
    ;

enum_variant
    : CAPNAME NL opt_nls
    | CAPNAME LPAREN field_params RPAREN NL opt_nls
    ;

field_params
    : field_param
    | field_params COMMA field_param
    ;

field_param
    : ident COLON type_expr opt_tags
    | type_expr
    ;

const_decl
    : CONST ident COLON type_expr ASSIGN expr NL opt_nls
    | CONST ident ASSIGN expr NL opt_nls
    ;

fn_decl
    : FN ident LPAREN opt_params RPAREN opt_return_type NL opt_nls fn_body END NL opt_nls
    ;

opt_params
    : %empty
    | param_list
    ;

param_list
    : param
    | param_list COMMA param
    ;

param
    : ident COLON type_expr opt_tags
    ;

opt_return_type
    : %empty
    | COLON type_expr opt_tags
    ;

fn_body
    : %empty
    | fn_body fn_stmt
    ;

fn_stmt
    : examples_block
    | promise_stmt
    | stmt
    ;

examples_block
    : EXAMPLES NL opt_nls stmts END NL opt_nls
    ;

promise_stmt
    : PROMISE expr NL opt_nls
    ;

test_decl
    : TEST TEXT NL opt_nls stmts END NL opt_nls
    ;

/* Types */

type_expr
    : type_atom
    | type_atom QMARK
    ;

type_atom
    : CAPNAME
    | CAPNAME LPAREN type_args RPAREN
    | LPAREN type_tuple_items RPAREN
    ;

type_tuple_items
    : type_expr COMMA type_expr
    | type_tuple_items COMMA type_expr
    ;

type_args
    : type_arg
    | type_args COMMA type_arg
    ;

type_arg
    : type_expr
    | TEXT
    | ident COLON type_expr opt_tags
    | ident COLON LBRACK tag_list RBRACK
    ;

/* Statements */

stmts
    : %empty
    | stmts stmt
    ;

stmt
    : VAR ident ASSIGN expr NL opt_nls
    | VAR ident COLON type_expr ASSIGN expr NL opt_nls
    | ASSERT expr NL opt_nls
    | RETURN NL opt_nls
    | RETURN pipe_expr NL opt_nls
    | RETURN pipe_expr IF expr NL opt_nls
    | RETURN if_inline_expr NL opt_nls
    | BREAK opt_guard NL opt_nls
    | CONTINUE opt_guard NL opt_nls
    | STOP opt_expr NL opt_nls
    | FOR for_target IN expr NL opt_nls stmts END NL opt_nls
    | WHILE expr NL opt_nls stmts END NL opt_nls
    | expr ASSIGN expr NL opt_nls
    | expr NL opt_nls
    ;

opt_expr
    : %empty
    | expr
    ;

opt_guard
    : %empty
    | IF expr
    ;

for_target
    : ident
    | UNDERSCORE
    | LPAREN for_target_list RPAREN
    ;

for_target_list
    : for_target COMMA for_target
    | for_target_list COMMA for_target
    ;

/* Expressions (strictly stratified by precedence; no %left/%right) */

expr
    : pipe_expr
    | if_inline_expr
    ;

pipe_expr
    : or_expr
    | pipe_expr PIPE or_expr
    ;

or_expr
    : and_expr
    | or_expr OR and_expr
    ;

and_expr
    : not_expr
    | and_expr AND not_expr
    ;

not_expr
    : cmp_expr
    | NOT not_expr
    ;

cmp_expr
    : coalesce_expr
    | coalesce_expr EQ coalesce_expr
    | coalesce_expr NE coalesce_expr
    | coalesce_expr LT coalesce_expr
    | coalesce_expr LE coalesce_expr
    | coalesce_expr GT coalesce_expr
    | coalesce_expr GE coalesce_expr
    | coalesce_expr IS coalesce_expr
    ;

coalesce_expr
    : add_expr
    | add_expr QQ coalesce_expr
    ;

add_expr
    : mul_expr
    | add_expr PLUS mul_expr
    | add_expr MINUS mul_expr
    ;

mul_expr
    : unary_expr
    | mul_expr STAR unary_expr
    | mul_expr SLASH unary_expr
    | mul_expr PERCENT unary_expr
    ;

unary_expr
    : postfix_expr
    | MINUS unary_expr
    | TRY unary_expr
    ;

postfix_expr
    : primary_expr
    | postfix_expr DOT member_name
    | postfix_expr LPAREN opt_call_args RPAREN
    | postfix_expr LBRACK expr RBRACK
    ;

primary_expr
    : INT
    | DECIMAL
    | DATE
    | TIMESTAMP
    | TEXT
    | interp_text
    | ATOM
    | TRUE
    | FALSE
    | NONE
    | ident
    | CAPNAME
    | UNDERSCORE
    | DOT member_name
    | DOT
    | LPAREN expr RPAREN
    | LPAREN tuple_items RPAREN
    | LBRACK opt_expr_list RBRACK
    | LBRACE opt_map_entries RBRACE
    | if_block_expr
    | case_expr
    | table_lit
    | lambda_expr
    ;

interp_text
    : TEXT_HEAD expr interp_tail
    ;

interp_tail
    : TEXT_TAIL
    | TEXT_MID expr interp_tail
    ;

tuple_items
    : expr COMMA expr
    | tuple_items COMMA expr
    ;

opt_expr_list
    : %empty
    | expr_list
    ;

expr_list
    : expr
    | expr_list COMMA expr
    ;

opt_map_entries
    : %empty
    | map_entries
    ;

map_entries
    : map_entry
    | map_entries COMMA map_entry
    ;

map_entry
    : expr COLON expr
    ;

opt_call_args
    : %empty
    | call_args
    ;

call_args
    : call_arg
    | call_args COMMA call_arg
    ;

call_arg
    : expr
    | ident COLON expr
    ;

/* Inline and block `if` expressions */

if_inline_expr
    : IF pipe_expr COLON expr opt_nls if_inline_tail
    ;

if_inline_tail
    : ELSE COLON expr
    | ELSE IF pipe_expr COLON expr opt_nls if_inline_tail
    ;

if_block_expr
    : IF expr NL opt_nls stmts if_block_tail END
    ;

if_block_tail
    : %empty
    | ELSE NL opt_nls stmts
    | ELSE IF expr NL opt_nls stmts if_block_tail
    ;

/* `case` expressions (flat arm/stmt sequence, LR(1)-unambiguous like Mo) */

case_expr
    : CASE expr NL opt_nls case_lines END
    ;

case_lines
    : case_line
    | case_lines case_line
    ;

case_line
    : unary_expr COLON NL opt_nls
    | unary_expr COLON expr NL opt_nls
    | stmt
    ;

/* Anonymous functions */

lambda_expr
    : FN LPAREN opt_lambda_params RPAREN expr END
    | FN LPAREN opt_lambda_params RPAREN NL opt_nls stmts END
    ;

opt_lambda_params
    : %empty
    | lambda_params
    ;

lambda_params
    : ident
    | UNDERSCORE
    | lambda_params COMMA ident
    | lambda_params COMMA UNDERSCORE
    ;

/* Markdown Table Literals */

table_lit
    : TABLE NL opt_nls BAR table_header BAR NL opt_nls table_rows END
    ;

table_header
    : ident
    | table_header BAR ident
    ;

table_rows
    : %empty
    | table_rows BAR table_cells BAR NL opt_nls
    ;

table_cells
    : expr
    | table_cells BAR expr
    ;

%%
