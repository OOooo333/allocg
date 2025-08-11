(* lib/ast_printer.ml *)

open Ast

(* 将类型转换为字符串 *)
let string_of_typ = function
  | IntType -> "int"
  | VoidType -> "void"

(* 将二元运算符转换为字符串 *)
let string_of_binop = function
  | OpAdd -> "+"
  | OpSub -> "-"
  | OpMul -> "*"
  | OpDiv -> "/"
  | OpMod -> "%"
  | OpEq  -> "=="
  | OpNeq -> "!="
  | OpLt  -> "<"
  | OpLe  -> "<="
  | OpGt  -> ">"
  | OpGe  -> ">="
  | OpAnd -> "&&"
  | OpOr  -> "||"

(* 将一元运算符转换为字符串 *)
let string_of_unop = function
  | OpNeg -> "-"
  | OpNot -> "!"
  | OpPlus -> "+"   (* 补全一元加号 *)

(* 递归函数，将表达式 AST 转换为节点风格的字符串 *)
let rec string_of_expr = function
  | IntLit n -> Printf.sprintf "IntLit(%d)" n
  | Var s -> Printf.sprintf "Var(%s)" s
  | Call (fname, args) ->
      Printf.sprintf "Call(%s, [%s])" fname
        (String.concat "; " (List.map string_of_expr args))
  | BinOp (op, e1, e2) ->
      Printf.sprintf "BinOp(%s, %s, %s)" (string_of_binop op)
        (string_of_expr e1) (string_of_expr e2)
  | UnOp (op, e) ->
      Printf.sprintf "UnOp(%s, %s)" (string_of_unop op) (string_of_expr e)

(* 递归函数，将语句 AST 转换为带缩进的、节点风格的字符串 *)
(* 递归函数，将语句 AST 转换为带缩进的、节点风格的字符串 *)
let rec string_of_stmt level stmt =
  let current_indent = String.make (level * 2) ' ' in
  let next_indent = String.make ((level + 1) * 2) ' ' in

  let stmt_str = match stmt with
    | Block stmts ->
        let stmts_str =
          if stmts = [] then ""
          else "\n" ^ (List.map (string_of_stmt (level + 1)) stmts |> String.concat ",\n") ^ "\n" ^ current_indent
        in
        Printf.sprintf "Block([%s])" stmts_str
    | Expr e -> Printf.sprintf "Expr(%s)" (string_of_expr e)
    | VarDecl (typ, name, init_opt) ->
        let init_str = match init_opt with
          | Some init -> Printf.sprintf "Some(%s)" (string_of_expr init)
          | None -> "None"
        in
        Printf.sprintf "VarDecl(%s, %s, %s)" (string_of_typ typ) name init_str
    | Assign (name, e) -> Printf.sprintf "Assign(%s, %s)" name (string_of_expr e)
    | If (cond, then_stmt, else_opt) ->
        let else_str = match else_opt with
          | Some s -> ",\n" ^ (string_of_stmt (level + 1) s) (* 调整了缩进的处理方式 *)
          | None -> ""
        in
        (* 修正: 格式化字符串现在有 4 个 %s，并提供了 4 个参数 *)
        Printf.sprintf "If(\n%s%s,\n%s%s%s\n%s)"
          next_indent (string_of_expr cond)
          next_indent (string_of_stmt (level + 1) then_stmt)
          else_str
          current_indent
    | While (cond, body) ->
        (* 修正: 格式化字符串现在有 4 个 %s，并提供了 4 个参数 *)
        Printf.sprintf "While(\n%s%s,\n%s%s\n%s)"
          next_indent (string_of_expr cond)
          next_indent (string_of_stmt (level + 1) body)
          current_indent
    | Break -> "Break"
    | Continue -> "Continue"
    | Return e_opt ->
        let e_str = match e_opt with
          | Some e -> Printf.sprintf "Some(%s)" (string_of_expr e)
          | None -> "None"
        in
        Printf.sprintf "Return(%s)" e_str
    | EmptyStmt -> "EmptyStmt"
  in
  current_indent ^ stmt_str

  
(* 将函数定义 AST 转换为节点风格的字符串 *)
let string_of_func_def f =
  let params_str =
    List.map (fun p -> Printf.sprintf "{ typ: %s, name: %s }" (string_of_typ p.ptyp) p.pname) f.params
    |> String.concat ", "
  in
  Printf.sprintf "FuncDef {\n  ftyp: %s;\n  fname: %s;\n  params: [%s];\n  body: %s\n}"
    (string_of_typ f.ftyp)
    f.fname
    params_str
    (string_of_stmt 1 f.body) (* 函数体从缩进1开始 *)

(* 顶层函数，将整个编译单元 AST 转换为字符串 *)
let string_of_comp_unit (prog: comp_unit) : string =
  "Program ([\n" ^
  (List.map string_of_func_def prog |> String.concat ",\n") ^
  "\n])\n"