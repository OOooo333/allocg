open ToyCtest

(* Read all input from stdin *)
let read_all_input () =
  let rec aux acc =
    try
      let line = input_line stdin in
      aux (line :: acc)
    with End_of_file -> String.concat "\n" (List.rev acc)
  in
  aux []

(* Parse program from a string *)
let parse_program (s : string) =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "stdin" };
  try
    Parser.program Lexer.token lexbuf
  with
  | Lexer.Error msg ->
      let pos = lexbuf.lex_curr_p in
      Printf.eprintf "Lexical error at line %d, column %d: %s\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) msg;
      exit 1
  | Parser.Error ->
      let pos = lexbuf.lex_curr_p in
      let tok = Lexing.lexeme lexbuf in
      Printf.eprintf "Syntax error at line %d, column %d: unexpected token '%s'\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1) tok;
      exit 1

let () =
  Printexc.record_backtrace true;

  let source = read_all_input () in

  (* Step 1: parse *)
  let ast =
    try parse_program source
    with Semantic.SemanticError msg ->
      Printf.eprintf "Semantic error: %s\n" msg;
      exit 1
  in

  (* Step 2: semantic check *)
  begin
    try Semantic.check_program ast
    with Semantic.SemanticError msg ->
      Printf.eprintf "Semantic error: %s\n" msg;
      exit 1
  end;

  (* Step 3: IR generation *)
  let ir = Ast_to_ir.generate ast in

  (* Step 4: IR to assembly *)
  let asm = Ir_to_asm.compile_program ir in

  (* Step 5: print to stdout *)
  Printf.printf "%s\n" asm
