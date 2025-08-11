open Ir

let string_of_operand = function
  | Const n -> string_of_int n
  | Temp i -> "t" ^ string_of_int i
  | Name s -> s

let string_of_instr instr =
  match instr with
  | BinOp { dest; op; src1; src2 } ->
      Printf.sprintf "  %s = %s %s %s"
        (string_of_operand dest)
        (string_of_operand src1)
        (Semantic.string_of_binop op) 
        (string_of_operand src2)
  | UnOp { dest; op; src } ->
      Printf.sprintf "  %s = %s%s"
        (string_of_operand dest)
        (Semantic.string_of_unop op) 
        (string_of_operand src)
  | Load { dest; src_addr } ->
      Printf.sprintf "  %s = load %s" (string_of_operand dest) (string_of_operand src_addr)
  | Store { dest_addr; src } ->
      Printf.sprintf "  store %s, %s" (string_of_operand dest_addr) (string_of_operand src)
  | Move { dest; src } ->
      Printf.sprintf "  %s = %s" (string_of_operand dest) (string_of_operand src)
  | Label s -> s ^ ":"
  | Jump s -> "  jump " ^ s
  | CJump { cond; label_true; label_false } ->
      Printf.sprintf "  if %s then jump %s else jump %s"
        (string_of_operand cond) label_true label_false
  | Call { dest; name; args } ->
      let args_str = List.map string_of_operand args |> String.concat ", " in
      (match dest with
      | Some d -> Printf.sprintf "  %s = call %s(%s)" (string_of_operand d) name args_str
      | None -> Printf.sprintf "  call %s(%s)" name args_str)
  | Return opt ->
      (match opt with
      | Some op -> "  return " ^ (string_of_operand op)
      | None -> "  return")

let string_of_ir_func (f: ir_func) =
  let params_str = String.concat ", " f.params in
  let body_str = List.map string_of_instr f.body |> String.concat "\n" in
  Printf.sprintf "func %s(%s):\n%s" f.name params_str body_str

let string_of_ir_program (prog: ir_program) =
  List.map string_of_ir_func prog |> String.concat "\n\n"