(* regalloction.ml *)
open Ir

(* 添加缺失的 string_of_operand 函数 *)
let string_of_operand = function
  | Const n -> string_of_int n
  | Temp i -> "t" ^ string_of_int i
  | Name s -> s

module OperandKey = struct
  type t = operand
  let equal a b = match (a, b) with
    | Const x, Const y -> x = y
    | Temp x, Temp y -> x = y
    | Name x, Name y -> x = y
    | _ -> false
  let hash = function
    | Const i -> Hashtbl.hash i
    | Temp i -> Hashtbl.hash i
    | Name s -> Hashtbl.hash s
end

module OperandHashtbl = Hashtbl.Make(OperandKey)

type interval = {
  operand: operand;
  mutable start: int;
  mutable end_: int;
  mutable reg: string option;  (* 分配的物理寄存器 *)
  mutable spilled: bool;       (* 是否溢出到栈上 *)
}

let k_registers = 16  (* 可用的物理寄存器数量 *)
let physical_registers = [|
  "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
  "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"; "s0";
|]

let spill_offset = ref 0
let spill_map : (operand, int) Hashtbl.t = Hashtbl.create 32

let allocate_spill_slot op =
  if not (Hashtbl.mem spill_map op) then begin
    spill_offset := !spill_offset + 4;
    Hashtbl.add spill_map op !spill_offset
  end;
  Hashtbl.find spill_map op

let build_intervals (func : ir_func) : interval list =
  let intervals = Hashtbl.create 32 in
  let counter = ref 0 in
  
  let process_operand pos op =
    match op with
    | Const _ -> ()  (* 常量不需要寄存器 *)
    | _ ->
        try
          let itv = Hashtbl.find intervals op in
          itv.start <- min itv.start pos;
          itv.end_ <- max itv.end_ pos
        with Not_found ->
          let itv = {
            operand = op;
            start = pos;
            end_ = pos;
            reg = None;
            spilled = false;
          } in
          Hashtbl.add intervals op itv
  in
  
  List.iteri (fun i instr ->
    counter := i;
    match instr with
    (* 修复模式匹配：添加缺失的字段并使用 _ 忽略不需要的字段 *)
    | BinOp { dest; src1; src2; op = _ } ->  (* 忽略 op 字段 *)
        process_operand i dest;
        process_operand i src1;
        process_operand i src2
    | UnOp { dest; src; op = _ } ->          (* 忽略 op 字段 *)
        process_operand i dest;
        process_operand i src
    | Move { dest; src } ->
        process_operand i dest;
        process_operand i src
    | Load { dest; src_addr } ->
        process_operand i dest;
        process_operand i src_addr
    | Store { dest_addr; src } ->
        process_operand i dest_addr;
        process_operand i src
    | CJump { cond; label_true = _; label_false = _ } ->  (* 忽略 label 字段 *)
        process_operand i cond
    | Call { dest; args; name = _ } ->        (* 忽略 name 字段 *)
        Option.iter (process_operand i) dest;
        List.iter (process_operand i) args
    | Return op_opt ->
        Option.iter (process_operand i) op_opt
    | _ -> ()  (* Label, Jump 等指令不处理操作数 *)
  ) func.body;
  
  Hashtbl.fold (fun _ itv acc -> itv :: acc) intervals []

let linear_scan_alloc (intervals : interval list) =
  let active = ref [] in
  let sorted_intervals = List.sort (fun a b -> compare a.start b.start) intervals in
  
  List.iter (fun itv ->
    (* 回收已结束的寄存器 *)
    active := List.filter (fun active_itv ->
      if active_itv.end_ >= itv.start then true
      else false
    ) !active;
    
    if List.length !active < k_registers then (
      (* 分配物理寄存器 *)
      let used_regs = List.filter_map (fun itv -> itv.reg) !active in
      let avail_reg = 
        Array.find_opt (fun r -> not (List.mem r used_regs)) physical_registers
      in
      match avail_reg with
      | Some reg ->
          itv.reg <- Some reg;
          active := itv :: !active
      | None -> 
          itv.spilled <- true  (* 没有可用寄存器，溢出 *)
    ) else (
      (* 需要溢出 *)
      let spill_candidate = 
        List.fold_left (fun candidate active_itv ->
          if active_itv.end_ > candidate.end_ then active_itv
          else candidate
        ) (List.hd !active) (List.tl !active)
      in
      
      if spill_candidate.end_ > itv.end_ then (
        (* 溢出候选者 *)
        spill_candidate.reg <- None;
        spill_candidate.spilled <- true;
        active := List.filter (fun itv -> itv != spill_candidate) !active;
        
        let used_regs = List.filter_map (fun itv -> itv.reg) !active in
        let avail_reg = 
          Array.find_opt (fun r -> not (List.mem r used_regs)) physical_registers
        in
        match avail_reg with
        | Some reg ->
            itv.reg <- Some reg;
            active := itv :: !active
        | None -> 
            itv.spilled <- true
      ) else (
        (* 溢出当前区间 *)
        itv.spilled <- true
      )
    )
  ) sorted_intervals

let apply_allocation (func : ir_func) (intervals : interval list) : ir_func * (operand -> string) =
  let reg_map = Hashtbl.create 32 in
  let get_reg op = 
    try Hashtbl.find reg_map op
    with Not_found -> 
      match op with
      | Const i -> string_of_int i
      | _ -> failwith ("Unallocated operand: " ^ string_of_operand op)
  in
  
  (* 构建寄存器映射 *)
  List.iter (fun itv ->
    if not itv.spilled then
      match itv.reg with
      | Some r -> Hashtbl.add reg_map itv.operand r
      | None -> ()  (* 已溢出的操作数 *)
  ) intervals;
  
  (* 生成新的函数体，插入加载/存储指令 *)
  let new_body = ref [] in
  let counter = ref 0 in
  
  let emit instr = new_body := instr :: !new_body in
  let get_temp () = 
    let t = Temp !counter in
    counter := !counter + 1;
    t
  in
  
  List.iter (fun instr ->
    match instr with
    | BinOp { dest; op; src1; src2 } ->
        let src1' = 
          if Hashtbl.mem spill_map src1 then
            let temp = get_temp () in
            emit (Load { dest = temp; src_addr = Name (get_reg src1) });
            temp
          else src1
        in
        let src2' = 
          if Hashtbl.mem spill_map src2 then
            let temp = get_temp () in
            emit (Load { dest = temp; src_addr = Name (get_reg src2) });
            temp
          else src2
        in
        let dest' = 
          if Hashtbl.mem spill_map dest then
            get_temp ()
          else dest
        in
        emit (BinOp { dest = dest'; op; src1 = src1'; src2 = src2' });
        
        if Hashtbl.mem spill_map dest then
          emit (Store { dest_addr = Name (get_reg dest); src = dest' })
    
    | UnOp { dest; op; src } ->
        let src' = 
          if Hashtbl.mem spill_map src then
            let temp = get_temp () in
            emit (Load { dest = temp; src_addr = Name (get_reg src) });
            temp
          else src
        in
        let dest' = 
          if Hashtbl.mem spill_map dest then
            get_temp ()
          else dest
        in
        emit (UnOp { dest = dest'; op; src = src' });
        
        if Hashtbl.mem spill_map dest then
          emit (Store { dest_addr = Name (get_reg dest); src = dest' })
    
    | Move { dest; src } ->
        let src' = 
          if Hashtbl.mem spill_map src then
            let temp = get_temp () in
            emit (Load { dest = temp; src_addr = Name (get_reg src) });
            temp
          else src
        in
        let dest' = 
          if Hashtbl.mem spill_map dest then
            get_temp ()
          else dest
        in
        emit (Move { dest = dest'; src = src' });
        
        if Hashtbl.mem spill_map dest then
          emit (Store { dest_addr = Name (get_reg dest); src = dest' })
    
    | _ -> emit instr  (* 其他指令直接传递 *)
  ) (List.rev func.body);
  
  let allocated_func = {
    name = func.name;
    params = func.params;
    body = List.rev !new_body;
  } in
  
  (allocated_func, get_reg)

let allocate_registers (func : ir_func) : ir_func * (operand -> string) =
  spill_offset := 0;
  Hashtbl.clear spill_map;
  
  let intervals = build_intervals func in
  linear_scan_alloc intervals;
  
  (* 为溢出的操作数分配栈空间 *)
  List.iter (fun itv ->
    if itv.spilled then
      ignore (allocate_spill_slot itv.operand)
  ) intervals;
  
  apply_allocation func intervals