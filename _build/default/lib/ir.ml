open Ast

(* --- 1. 操作数定义 --- *)
(* 操作数代表指令可以操作的值 *)
type operand =
  | Const of int          (* 立即数常量, e.g., 5 *)
  | Temp of int           (* 临时变量 (虚拟寄存器), e.g., t1, t2. 这是寄存器分配的主要对象。 *)
  | Name of string        (* 源码中的命名变量, e.g., "x", "g". 后续会被映射到栈或全局数据区。 *)


(* --- 2. IR 指令集定义 --- *)
type instr =
  (* 运算指令 (只操作虚拟寄存器和常量) *)
  | BinOp of { dest: operand; op: binop; src1: operand; src2: operand } (* dest = src1 op src2 *)
  | UnOp of { dest: operand; op: unop; src: operand }                   (* dest = op src *)
  
  (* 内存访问指令 *)
  | Load of { dest: operand; src_addr: operand }     (* dest = *src_addr, e.g., t1 = *x *)
  | Store of { dest_addr: operand; src: operand }    (* *dest_addr = src, e.g., *x = t1 *)
  
  (* 赋值/移动指令 *)
  | Move of { dest: operand; src: operand }          (* dest = src. 用于寄存器间传值或将常量加载到寄存器 *)

  (* 控制流指令 *)
  | Label of string                                  (* 定义标签, e.g., L1: *)
  | Jump of string                                   (* 无条件跳转, goto L1 *)
  | CJump of { cond: operand; label_true: string; label_false: string } (* if cond then goto L_true else goto L_false *)

  (* 函数调用指令 *)
  (* `dest` 用于接收返回值，是可选的 *)
  | Call of { dest: operand option; name: string; args: operand list }
  | Return of operand option

(* --- 3. IR 函数与程序定义 --- *)

(* 单个函数的中间表示 *)
type ir_func = {
  name: string;
  params: string list;  
  body: instr list;     (* 线性的指令列表 *)
}

(* 整个程序的中间表示 *)
type ir_program = ir_func list