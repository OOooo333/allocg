%{
open Ast
%}

(* 词法单元 (Token) 声明 *)
%token <int> INT_LITERAL
%token <string> ID
%token EOF

%token INT VOID
%token IF ELSE WHILE BREAK CONTINUE RETURN

%token ASSIGN SEMI COMMA
%token LPAREN RPAREN LBRACE RBRACE

%token PLUS MINUS TIMES DIVIDE MOD
%token EQ NEQ LT LE GT GE
%token AND OR NOT

(* 优先级与结合性声明。*)
%nonassoc NOELSE (* 用于解决悬挂else问题 *)
%nonassoc ELSE

%left OR          (* or 是左结合，优先级最低 *)
%left AND         (* and 是左结合 *)
%nonassoc EQ NEQ  (* 比较运算符无结合性 *)
%nonassoc LT LE GT GE 
%left PLUS MINUS  (* 加减法是左结合 *)
%left TIMES DIVIDE MOD (* 乘除模是左结合 *)
%right NOT UMINUS UPLUS (* 一元运算符是右结合，优先级最高。UMINUS是为一元减号设定的一个虚拟标记，UPLUS是为一元加号设定的一个虚拟标记 *)

(* 开始符号 *)
%start <Ast.comp_unit> program

%%

(* 顶层规则: 一个程序由零个或多个函数定义组成 *)
program:
  | list(func) EOF { $1 }

(* 函数定义规则 *)
func:
  | typ ID LPAREN param_list RPAREN block
    { { ftyp = $1;
        fname = $2;
        params = $4;
        body = $6 } }

(* 代码块规则 *)
block:
  | LBRACE list(stmt) RBRACE { Block $2 }

(* 参数列表规则 *)
param_list:
  | (* empty *)                                    { [] }
  | VOID                                           { [] }
  | separated_nonempty_list(COMMA, param)          { $1 }

(* 单个参数规则 *)
param:
  | typ ID { { ptyp = $1; pname = $2 } }

(* 基本类型规则 *)
typ:
  | INT { IntType }
  | VOID { VoidType }

(* 语句规则 *)
stmt:
  | SEMI                                            { EmptyStmt }
  | expr SEMI                                       { Expr $1 }
  | var_decl                                        { $1 }
  | ID ASSIGN expr SEMI                             { Assign($1, $3) }
  | block                                           { $1 }
  | IF LPAREN expr RPAREN stmt %prec NOELSE         { If($3, $5, None) }
  | IF LPAREN expr RPAREN stmt ELSE stmt            { If($3, $5, Some $7) }
  | WHILE LPAREN expr RPAREN stmt                   { While($3, $5) }
  | BREAK SEMI                                      { Break }
  | CONTINUE SEMI                                   { Continue }
  | RETURN SEMI                                     { Return None }
  | RETURN expr SEMI                                { Return (Some $2) }

(* 变量声明规则 *)
var_decl:
  | typ ID SEMI
    { VarDecl($1, $2, None) }
  | typ ID ASSIGN expr SEMI
    { VarDecl($1, $2, Some $4) }

(* 表达式规则 *)
expr:
  | expr OR expr          { BinOp(OpOr, $1, $3) }
  | expr AND expr         { BinOp(OpAnd, $1, $3) }
  | expr EQ expr          { BinOp(OpEq, $1, $3) }
  | expr NEQ expr         { BinOp(OpNeq, $1, $3) }
  | expr LT expr          { BinOp(OpLt, $1, $3) }
  | expr LE expr          { BinOp(OpLe, $1, $3) }
  | expr GT expr          { BinOp(OpGt, $1, $3) }
  | expr GE expr          { BinOp(OpGe, $1, $3) }
  | expr PLUS expr        { BinOp(OpAdd, $1, $3) }
  | expr MINUS expr       { BinOp(OpSub, $1, $3) }
  | expr TIMES expr       { BinOp(OpMul, $1, $3) }
  | expr DIVIDE expr      { BinOp(OpDiv, $1, $3) }
  | expr MOD expr         { BinOp(OpMod, $1, $3) }
  | NOT expr              { UnOp(OpNot, $2) }
  | MINUS expr %prec UMINUS { UnOp(OpNeg, $2) } (* 使用 %prec UMINUS 赋予其一元运算符的最高优先级 *)
  | PLUS expr %prec UPLUS   { UnOp(OpPlus, $2) } (* 新增一元加号规则 *)
  | primary               { $1 }

(* 优先级最高的表达式单元 *)
primary:
  | INT_LITERAL                                   { IntLit $1 }
  | ID                                            { Var $1 }
  | ID LPAREN separated_list(COMMA, expr) RPAREN  { Call($1, $3) }
  | LPAREN expr RPAREN                            { $2 }

%%