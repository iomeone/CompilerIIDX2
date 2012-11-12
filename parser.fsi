// Signature file for parser generated by fsyacc
module Parser
type token = 
  | EOF
  | RPAREN
  | LPAREN
  | SEMICOLON
  | LESS_MINUS
  | DOT
  | ARRAY_CREATE
  | COMMA
  | REC
  | IN
  | LET
  | IDENT of (Id.t)
  | SQRT
  | ELSE
  | THEN
  | IF
  | GREATER
  | LESS
  | GREATER_EQUAL
  | LESS_EQUAL
  | LESS_GREATER
  | EQUAL
  | SLASH_DOT
  | AST_DOT
  | PLUS_DOT
  | MINUS_DOT
  | SLASH
  | AST
  | PLUS
  | MINUS
  | NOT
  | FLOAT of (float)
  | INT of (int)
  | BOOL of (bool)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_RPAREN
    | TOKEN_LPAREN
    | TOKEN_SEMICOLON
    | TOKEN_LESS_MINUS
    | TOKEN_DOT
    | TOKEN_ARRAY_CREATE
    | TOKEN_COMMA
    | TOKEN_REC
    | TOKEN_IN
    | TOKEN_LET
    | TOKEN_IDENT
    | TOKEN_SQRT
    | TOKEN_ELSE
    | TOKEN_THEN
    | TOKEN_IF
    | TOKEN_GREATER
    | TOKEN_LESS
    | TOKEN_GREATER_EQUAL
    | TOKEN_LESS_EQUAL
    | TOKEN_LESS_GREATER
    | TOKEN_EQUAL
    | TOKEN_SLASH_DOT
    | TOKEN_AST_DOT
    | TOKEN_PLUS_DOT
    | TOKEN_MINUS_DOT
    | TOKEN_SLASH
    | TOKEN_AST
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_NOT
    | TOKEN_FLOAT
    | TOKEN_INT
    | TOKEN_BOOL
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startexp
    | NONTERM_simple_exp
    | NONTERM_exp
    | NONTERM_fundef
    | NONTERM_formal_args
    | NONTERM_actual_args
    | NONTERM_elems
    | NONTERM_pat
/// This function maps integers indexes to symbolic token ids
val tagOfToken: token -> int

/// This function maps integers indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val exp : (Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> (Syntax.t) 
