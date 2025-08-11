
(* The type of tokens. *)

type token = 
  | WHILE
  | VOID
  | TIMES
  | SEMI
  | RPAREN
  | RETURN
  | RBRACE
  | PLUS
  | OR
  | NOT
  | NEQ
  | MOD
  | MINUS
  | LT
  | LPAREN
  | LE
  | LBRACE
  | INT_LITERAL of (int)
  | INT
  | IF
  | ID of (string)
  | GT
  | GE
  | EQ
  | EOF
  | ELSE
  | DIVIDE
  | CONTINUE
  | COMMA
  | BREAK
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.comp_unit)
