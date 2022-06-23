module AST

(* Values *)
type Int = int32
type Value =
    | Int of Int
    | True
    | False

(* Binary operators *)
type BinOp =
    | Gt  | Lt  | Eq  | NEq | GEq | LEq // Comparision, relational
    | Add | Sub | Mul | Div | Mod // Arithmetic
    | BitAnd | BitOr  | Xor // Bitwise
    | LogAnd | LogOr // Logical

(* Unary operator *)
type UnaryOp = Not

(* Variable identifiers *)
type VarName = string

(* Left values, to the left of an update operator *)
type LValue =
    | Var of VarName
    | Lookup of VarName * Exp // array access
    | Rec of VarName * LValue // specify part of record to update/manipulate

(* Expressions *)
and Exp =
    | Const of Value
    | LVal of LValue
    | UnaryOp of UnaryOp * Exp
    | BinOp of BinOp * Exp * Exp

(* Update operators *)
type UpdateOp =
    | AddEq
    | SubEq
    | Swap

(* Procedure identifiers *)
type ProcName = string

(* Statements *)
type Stmt =
    | Assign of UpdateOp * LValue * Exp
    | If     of Exp * Stmt * Stmt * Exp // IF e1 THEN s1 ELSE s2 FI e2
    | DoLoop of Exp * Stmt * Stmt * Exp // FROM e1 DO s1 {LOOP s2} UNTIL e2
    | Call   of ProcName
    | Uncall of ProcName
    | Skip
    | Sequence of Stmt list

(* Variable declarations *)
type VDec =
    | Scalar of VarName * Value
    | Array of VarName * Int
    | RecordD of VarName * VDec list

(* Main procedure *
 * Consists of zero or more variable declarations and statements *)
type MainProc =
    | MainProc of VDec list * Stmt list

(* Procedures *
 * Consists of a name, zero or more variable declarations and statements *)
type Proc = {
    name : ProcName
    vdecls : VDec list
    stmts : Stmt list
}

(* A program is a main procedure and zero or more procedures *)
type Program =
    | Program of MainProc * Proc list

