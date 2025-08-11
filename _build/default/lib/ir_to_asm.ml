
(* ir_to_asm.ml *)
open Ir
open Ast
open Regalloction  (* 确保打开寄存器分配模块 *)

let stack_offset = ref 0
let var_env = Hashtbl.create 1600

let get_stack_offset var =
  try Hashtbl.find var_env var
  with Not_found -> failwith ("Unknown variable: " ^ var)

let alloc_stack var =
  try get_stack_offset var
  with _ ->
    stack_offset := !stack_offset + 4;
    Hashtbl.add var_env var !stack_offset;
    !stack_offset

(* 使用寄存器分配后的 get_reg 函数 *)
let operand_to_str get_reg op = 
  match op with
  | Const i -> string_of_int i
  | Temp i -> get_reg (Temp i)
  | Name s -> get_reg (Name s)

let load_operand get_reg reg op =
  match op with
  | Const i -> Printf.sprintf "\tli %s, %d\n" reg i
  | _ -> 
      let loc = operand_to_str get_reg op in
      Printf.sprintf "\tlw %s, %s\n" reg loc

let compile_instr get_reg (instr : instr) =
  match instr with
  | Move { dest = Name s; src } ->
      let dst_off = alloc_stack s in
      let load_src = load_operand get_reg "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Move { dest = Temp n; src } ->
      let dst_off = alloc_stack ("t" ^ string_of_int n) in
      let load_src = load_operand get_reg "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Move { dest = Const _; src = _ } ->
      failwith "Cannot move to a constant operand"
  | BinOp { dest; op; src1; src2 } ->
      let dst_off =
        alloc_stack
          (match dest with Temp n -> "t" ^ string_of_int n | Name s -> s | _ -> failwith "Bad dest")
      in
      let lhs_code = load_operand get_reg "t1" src1 in
      let rhs_code = load_operand get_reg "t2" src2 in
      let op_code =
        match op with
        | OpAdd -> "\tadd t0, t1, t2\n"
        | OpSub -> "\tsub t0, t1, t2\n"
        | OpMul -> "\tmul t0, t1, t2\n"
        | OpDiv -> "\tdiv t0, t1, t2\n"
        | OpMod -> "\trem t0, t1, t2\n"
        | OpEq  -> "\tsub t0, t1, t2\n\tseqz t0, t0\n"
        | OpNeq -> "\tsub t0, t1, t2\n\tsnez t0, t0\n"
        | OpLt  -> "\tslt t0, t1, t2\n"
        | OpGt  -> "\tsgt t0, t1, t2\n"
        | OpLe  -> "\tsgt t0, t1, t2\n\txori t0, t0, 1\n"
        | OpGe  -> "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
        | OpAnd -> "\tand t0, t1, t2\n"
        | OpOr  -> "\tor t0, t1, t2\n"
      in
      lhs_code ^ rhs_code ^ op_code ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | UnOp { dest; op; src } ->
      let dst_off =
        alloc_stack
          (match dest with Temp n -> "t" ^ string_of_int n | Name s -> s | _ -> failwith "Bad dest")
      in
      let load_src = load_operand get_reg "t1" src in
      let op_code =
        match op with
        | OpNeg -> "\tneg t0, t1\n"
        | OpNot -> "\tseqz t0, t1\n"
        | OpPlus -> "\tmv t0, t1\n"
      in
      load_src ^ op_code ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Load { dest; src_addr } ->
      let dst_off =
        alloc_stack
          (match dest with Temp n -> "t" ^ string_of_int n | Name s -> s | _ -> failwith "Bad dest")
      in
      let src_code = load_operand get_reg "t1" src_addr in
      src_code ^ "\tlw t0, 0(t1)\n" ^ Printf.sprintf "\tsw t0, %d(sp)\n" dst_off
  | Store { dest_addr; src } ->
      let dst_code = load_operand get_reg "t1" dest_addr in
      let src_code = load_operand get_reg "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
  | Label lbl -> Printf.sprintf "%s:\n" lbl
  | Jump lbl -> Printf.sprintf "\tj %s\n" lbl
  | CJump { cond; label_true; label_false } ->
      let cond_code = load_operand get_reg "t0" cond in
      cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n\tj %s\n" label_true label_false
  | Call { dest; name; args } ->
      let dst_off =
        match dest with
        | Some (Temp n) -> alloc_stack ("t" ^ string_of_int n)
        | Some (Name s) -> alloc_stack s
        | Some _ -> failwith "Bad dest"
        | None -> -1
      in
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then load_operand get_reg (Printf.sprintf "a%d" i) arg
            else
              let offset = 4 * (i - 8) in
              load_operand get_reg "t0" arg ^ Printf.sprintf "\tsw t0, %d(sp)\n" (-1600 - offset))
          args
        |> String.concat ""
      in
      let call_code = Printf.sprintf "\tcall %s\n" name in
      let ret_code =
        if dst_off <> -1 then Printf.sprintf "\tsw a0, %d(sp)\n" dst_off else ""
      in
      args_code ^ call_code ^ ret_code
  | Return op_opt ->
      let ra_offset = alloc_stack "ra" in
      let ret_code =
        match op_opt with
        | Some op -> load_operand get_reg "a0" op
        | None -> ""
      in
      ret_code ^ Printf.sprintf "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n" ra_offset

let compile_func (f : ir_func) : string =
  (* 执行寄存器分配并使用结果 *)
  let allocated_func, get_reg = allocate_registers f in
  
  Hashtbl.clear var_env;
  stack_offset := 0;

  let param_setup =
    List.mapi
      (fun i name ->
        let off = alloc_stack name in
        if i < 8 then Printf.sprintf "\tsw a%d, %d(sp)\n" i off
        else
          Printf.sprintf "\tlw t0, %d(sp)\n\tsw t0, %d(sp)\n"
            (-4 * (i - 8))
            off)
      allocated_func.params  (* 使用分配后的函数参数 *)
    |> String.concat ""
  in
  let param_setup =
    param_setup ^ Printf.sprintf "\tsw ra, %d(sp)\n" (alloc_stack "ra")
  in
  (* 使用分配后的函数体和 get_reg 函数 *)
  let body_code = allocated_func.body |> List.map (compile_instr get_reg) |> String.concat "" in
  let body_code =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code
      ^ Printf.sprintf
          "\tlw ra, %d(sp)\n\taddi sp, sp, 1600\n\tret\n"
          (get_stack_offset "ra")
    else body_code
  in
  let func_label = allocated_func.name in
  let prologue = Printf.sprintf "%s:\n\taddi sp, sp, -1600\n" func_label in
  prologue ^ param_setup ^ body_code

let compile_program (prog : ir_program) : string =
  let prologue = ".text\n .global main\n" in
  let body_asm =
    List.map compile_func prog |> String.concat "\n"
  in
  prologue ^ body_asm