open Ast

(* --- 1. 类型定义与环境 --- *)

(* 符号表中存储的值的类型 *)
type symbol_info =
  | VarInfo of { typ: typ }
  | FuncInfo of { return_type: typ; param_types: typ list }

(* 符号表: 从字符串标识符到信息的映射 *)
module SymbolMap = Map.Make(String)

(* 环境记录，用于在 AST 遍历时传递上下文信息 *)
type env = {
  (* 作用域栈：每个元素是一个作用域的符号表。栈顶是当前作用域。 *)
  var_scopes: symbol_info SymbolMap.t list;
  (* 全局函数符号表，只在第一遍扫描时构建 *)
  func_table: symbol_info SymbolMap.t;
  (* 当前正在检查的函数的返回类型 *)
  current_func_return_type: typ option;
  (* 标记是否在循环体内，用于检查 break/continue *)
  in_loop: bool;
}

(* 自定义语义错误异常 *)
exception SemanticError of string

(* 抛出错误的辅助函数 *)
let error msg = raise (SemanticError msg)

(* 辅助函数: 类型转字符串 (用于错误信息) *)
let string_of_typ = function
  | IntType -> "int"
  | VoidType -> "void"


(* 将二元运算符转换为字符串 (用于错误信息和打印) *)
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

(* 将一元运算符转换为字符串 (用于错误信息和打印) *)
let string_of_unop = function
  | OpNeg -> "-"
  | OpNot -> "!"
  | OpPlus -> "+"   (* 补全一元加号 *)

(* --- 2. 环境管理辅助函数 --- *)

(* 创建一个初始的空环境 *)
let initial_env () = {
  var_scopes = [SymbolMap.empty]; (* 栈底是全局作用域 *)
  func_table = SymbolMap.empty;
  current_func_return_type = None;
  in_loop = false;
}

(* 进入一个新的作用域 (例如进入一个 block) *)
let enter_scope env =
  { env with var_scopes = SymbolMap.empty :: env.var_scopes }

(* 离开一个作用域 *)
let leave_scope env =
  match env.var_scopes with
  | _ :: t -> { env with var_scopes = t }
  | [] -> failwith "内部错误：无法离开全局作用域" (* 理论上不应发生 *)

(* 在当前作用域 (栈顶) 声明一个新变量 *)
let add_var env id typ =
  let current_scope = List.hd env.var_scopes in
  if SymbolMap.mem id current_scope then
    error (Printf.sprintf "变量 '%s' 在此作用域中已被声明" id);
  
  let new_scope = SymbolMap.add id (VarInfo { typ }) current_scope in
  (* 返回更新了作用域栈的新环境 *)
  { env with var_scopes = new_scope :: (List.tl env.var_scopes) }

(* 查找一个变量，从当前作用域逐层向外查找 *)
let find_var env id =
  let rec find_in_scopes scopes =
    match scopes with
    | [] -> None (* 所有作用域都找完了，未找到 *)
    | h :: t ->
        match SymbolMap.find_opt id h with
        | Some info -> Some info (* 在当前作用域找到 *)
        | None -> find_in_scopes t (* 继续向外层作用域查找 *)
  in
  find_in_scopes env.var_scopes

(* 在全局函数表中声明一个新函数 *)
let add_func env (fdef: Ast.func_def) =
  if SymbolMap.mem fdef.fname env.func_table then
    error (Printf.sprintf "函数 '%s' 重复定义" fdef.fname);
  
  let param_types = List.map (fun p -> p.ptyp) fdef.params in
  let info = FuncInfo { return_type = fdef.ftyp; param_types } in
  { env with func_table = SymbolMap.add fdef.fname info env.func_table }

(* 在全局函数表中查找一个函数 *)
let find_func env name =
  SymbolMap.find_opt name env.func_table


(* --- 3. 表达式与语句的类型检查 --- *)

(* 表达式检查函数: 检查表达式并返回其类型 *)
let rec check_expr env expr : typ =
  match expr with
  | IntLit _ -> IntType
  | Var id ->
      (match find_var env id with
      | Some (VarInfo { typ }) -> typ
      | Some (FuncInfo _) -> error (Printf.sprintf "'%s' 是一个函数, 不能当作变量使用" id)
      | None -> error (Printf.sprintf "未声明的变量 '%s'" id))

  (* 适配: UnOp 构造函数和我们的 OpNeg/OpNot *)
  | UnOp (op, e) ->
      let typ = check_expr env e in
      (match op, typ with
      | (OpNeg | OpNot | OpPlus), IntType -> IntType
      | _, _ -> error "一元运算符只能作用于 int 类型")

  (* 适配: BinOp 构造函数 *)
  | BinOp (_, e1, e2) -> (* op 本身暂时不检查，因为所有二元运算都返回 int *)
      let t1 = check_expr env e1 in
      let t2 = check_expr env e2 in
      if t1 <> IntType || t2 <> IntType then
        error "二元运算符要求操作数都为 int 类型";
      IntType

  | Call (fname, args) ->
      (match find_func env fname with
      | Some (FuncInfo { return_type; param_types }) ->
          let arg_types = List.map (check_expr env) args in
          if List.length arg_types <> List.length param_types then
            error (Printf.sprintf "函数 '%s' 调用参数数量错误: 期望 %d, 得到 %d" 
              fname (List.length param_types) (List.length arg_types));
          List.iter2 (fun expected actual ->
            if expected <> actual then
              let msg = Printf.sprintf "函数 '%s' 调用参数类型不匹配: 期望 %s, 得到 %s"
                fname (string_of_typ expected) (string_of_typ actual)
              in error msg
          ) param_types arg_types;
          return_type
      | _ -> error (Printf.sprintf "未声明的函数 '%s'" fname))

(* 语句检查函数: 检查语句并返回更新后的环境 *)
let rec check_stmt env stmt : env =
  match stmt with
  | Block stmts ->
      let new_env = enter_scope env in
      (* 依次检查块内的所有语句, fold_left 会将更新后的 env 传递给下一个语句 *)
      let _ = List.fold_left check_stmt new_env stmts in
      leave_scope env (* 离开作用域，丢弃块内声明，返回原始 env *)

  | Expr e ->
      let _ = check_expr env e in (* 对表达式进行类型检查，但忽略其类型结果 *)
      env

  (* 适配: VarDecl(typ, string, expr option) *)
  | VarDecl (typ, id, init_opt) ->
      if typ = VoidType then
        error (Printf.sprintf "不能声明 void 类型的变量 '%s'" id);
      
      (match init_opt with
      | Some init_expr ->
          let init_type = check_expr env init_expr in
          if init_type <> typ then
            error (Printf.sprintf "变量 '%s' 初始化类型错误: 期望 %s, 但得到 %s"
                     id (string_of_typ typ) (string_of_typ init_type));
      | None -> () (* 没有初始化，无需检查 *)
      );
      add_var env id typ (* 将新变量加入当前作用域 *)

  | Assign (id, e) ->
      let var_info = find_var env id in
      (match var_info with
       | Some (VarInfo { typ = var_type }) ->
           let expr_type = check_expr env e in
           if var_type <> expr_type then
             error (Printf.sprintf "赋值类型不匹配: 无法将 %s 类型赋给 %s 类型的变量 '%s'"
                      (string_of_typ expr_type) (string_of_typ var_type) id);
           env
       | Some (FuncInfo _) -> error (Printf.sprintf "不能对函数 '%s' 进行赋值" id)
       | None -> error (Printf.sprintf "赋值给未声明的变量 '%s'" id))

  | If (cond, then_stmt, else_opt) ->
      if check_expr env cond <> IntType then
        error "if 条件必须是 int 类型";
      let _ = check_stmt env then_stmt in
      (match else_opt with
      | Some else_stmt -> let _ = check_stmt env else_stmt in ()
      | None -> ());
      env

  | While (cond, body) ->
      if check_expr env cond <> IntType then
        error "while 条件必须是 int 类型";
      (* 创建一个标记在循环内的新环境来检查循环体 *)
      let loop_env = { env with in_loop = true } in
      let _ = check_stmt loop_env body in
      env

  | Break | Continue ->
      if not env.in_loop then
        error "'break' 或 'continue' 语句必须在循环内";
      env

  (* 适配: Return of expr option *)
  | Return e_opt ->
      (match env.current_func_return_type with
      | Some IntType ->
          (match e_opt with
          | Some e -> if check_expr env e <> IntType then
                        error "return 语句的返回值类型与函数定义不符 (期望 int)"
          | None -> error "int 函数必须有返回值")
      | Some VoidType ->
          (match e_opt with
          | Some _ -> error "void 函数不能有返回值"
          | None -> () (* void 函数，无返回值，正确 *) )
      | None -> failwith "内部错误：return 语句不在函数体内");
      env

  | EmptyStmt -> env (* 空语句，合法，什么都不做 *)

(* --- 4. 顶层检查函数 --- *)

(* 函数定义检查 *)
let check_func_def env (fdef: Ast.func_def) =
  (* 创建一个此函数专用的新环境 *)
  let func_env = { env with
    var_scopes = [SymbolMap.empty]; (* 函数体开始时，变量作用域是空的 *)
    current_func_return_type = Some fdef.ftyp;
    in_loop = false;
  } in

  (* 将所有函数参数加入到函数体的顶层作用域中 *)
  let env_with_params =
    List.fold_left (fun current_env p ->
      add_var current_env p.pname p.ptyp
    ) func_env fdef.params
  in
  
  (* 检查函数体 *)
  let _ = check_stmt env_with_params fdef.body in
  ()

(* 整个程序检查 *)
let check_program (prog: Ast.comp_unit) =
  try
    (* 第一遍：收集所有函数签名到全局函数表中 *)
    let env_with_funcs = List.fold_left add_func (initial_env ()) prog in
    
    (* 检查是否存在一个合法的 main 函数 *)
    (match find_func env_with_funcs "main" with
    | Some (FuncInfo { return_type = IntType; param_types = [] }) -> ()
    | _ -> error "程序必须包含一个 'int main()' 函数作为入口点");

    (* 第二遍：逐个检查每个函数体内部的逻辑 *)
    List.iter (check_func_def env_with_funcs) prog;
    
    print_endline "语义分析通过！"
  with
  | SemanticError msg ->
    Printf.eprintf "语义错误: %s\n" msg;
    exit 1