{
open Parser
exception Error of string

let keywords = [
  ("int",      INT);
  ("void",     VOID);
  ("if",       IF);
  ("else",     ELSE);
  ("while",    WHILE);
  ("break",    BREAK);
  ("continue", CONTINUE);
  ("return",   RETURN);
]

}

(* 正则定义 *)
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha | '_') (alpha | digit | '_')*


rule token = parse
  (*  Whitespace and Newlines  *)
  | [' ' '\t' '\r'] { token lexbuf }                (* 跳过空格 *)
  | '\n'           { Lexing.new_line lexbuf; token lexbuf } (* 记录行数 *)

  (*  Comments  *)
  | "//" [^ '\n']* { token lexbuf }                (* 单行注释 *)
  | "/*"           { comment lexbuf }               (* 多行注释 *)

  (*  Integer Literals *)
  | digit+ as num  { INT_LITERAL (int_of_string num) }

  (*  Identifiers and Keywords *)
  | ident as id    {
      try List.assoc id keywords
      with Not_found -> ID id
    }

  (* 运算符与符号 *)
  | "=="                     { EQ }
  | "!="                     { NEQ }
  | "<="                     { LE }
  | ">="                     { GE }
  | '<'                      { LT }
  | '>'                      { GT }

  | "&&"                     { AND }
  | "||"                     { OR }
  | '!'                      { NOT }

  | '='                      { ASSIGN }
  | '+'                      { PLUS }
  | '-'                      { MINUS }
  | '*'                      { TIMES }
  | '/'                      { DIVIDE }
  | '%'                      { MOD }

  (* 分隔符 *)
  | '('                      { LPAREN }
  | ')'                      { RPAREN }
  | '{'                      { LBRACE }
  | '}'                      { RBRACE }
  | ';'                      { SEMI }
  | ','                      { COMMA }

  (* 文件结尾 *)
  | eof                      { EOF }

  (* 错误字符 *)
  (* | _ ->
      let pos = lexbuf.lex_curr_p in
      (* 使用 Lexing.lexeme 来获取匹配到的非法字符(串) *)
      let char_str = Lexing.lexeme lexbuf in
      let msg = Printf.sprintf "Unexpected character '%s'" char_str in
      raise (LexerError (msg, pos)) *)
   | _                        { raise (Error ("Unexpected character: " ^ Lexing.lexeme lexbuf)) }  

(* and comment = parse
  | "*/"           { token lexbuf } (* 结束多行注释 *)
  | '\n'           { Lexing.new_line lexbuf; comment lexbuf } (* Keep track of lines inside comments *)
  | eof            {
      let pos = lexbuf.lex_curr_p in
      raise (LexerError ("Unterminated multi-line comment", pos))
    }
  | _              { comment lexbuf } *)

and comment = parse
  | "*/"                     { token lexbuf }                    (* 结束多行注释 *)
  | eof                      { raise (Error "Unterminated comment") }
  | _                        { comment lexbuf }
