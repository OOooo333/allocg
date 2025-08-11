(* ast.ml *)

(* 类型定义 *)
type typ =
  | IntType
  | VoidType

(* 二元运算符 *)
type binop =
  (* 算术运算符 *)
  | OpAdd | OpSub | OpMul | OpDiv | OpMod
  (* 关系运算符 *)
  | OpEq | OpNeq | OpLt | OpLe | OpGt | OpGe
  (* 逻辑运算符 *)
  | OpAnd | OpOr

(* 一元运算符 *)
type unop =
  | OpNeg   (* 算术负号, -x *)
  | OpNot   (* 逻辑非, !x *)
  | OpPlus  (* 算术正号, +x *)   (* 新增一元加号 *)

(* 表达式 *)
type expr =
  | IntLit of int                 (* 整数常量 *)
  | Var of string                 (* 变量/标识符 *)
  | BinOp of binop * expr * expr  (* 二元运算 *)
  | UnOp of unop * expr           (* 一元运算 *)
  | Call of string * expr list    (* 函数调用 *)

(* 语句 *)
type stmt =
  | Block of stmt list            (* 语句块 {...} *)
  | EmptyStmt                     (* 空语句 ; *)
  | Expr of expr                  (* 表达式语句 *)
  | VarDecl of typ * string * expr option     (*变量声明，可以同时表示 'int a;' (None) 和 'int a = 5;' (Some (IntLit 5)*)
  | Assign of string * expr       (* 赋值语句 *)
  | If of expr * stmt * stmt option (* if-else, else 分支可选 *)
  | While of expr * stmt          (* while 循环 *)
  | Break   (*break*)
  | Continue    (*continue*)
  | Return of expr option         (* return, 返回值可选，以支持 'return;' 和 'return 5;' *)


(* 函数参数 *)
type param = {
  ptyp : typ;
  pname : string;
}

(* 函数定义 *)
type func_def = {
  ftyp : typ;                    (* 返回类型 *)
  fname : string;                  (* 函数名 *)
  params : param list;             (* 参数列表 *)
  body : stmt;                     (* 函数体 *)
}

(* 编译单元 *)
(* 整个程序的顶层结构，即一个函数定义的列表。 *)
type comp_unit = func_def list

