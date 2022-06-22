module JanusAST
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
    | Rec of VarName * LValue // only specify part of record to update/manipulate

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
    | If     of Exp * Stmt * Stmt * Exp // if e1 then s1 else s2 fi e2
    | DoLoop of Exp * Stmt * Stmt * Exp // from e1 do s1 {loop s2} until e2
    | Call   of ProcName
    | Uncall of ProcName
    | Skip
    | Sequence of Stmt list

type VDec =
    | Scalar of VarName * Value
    | Array of VarName * Int
    | RecordD of VarName * VDec list

type MainProc =
    | MainProc of VDec list * Stmt list

type Proc = {
    name : ProcName
    vdecls : VDec list
    stmts : Stmt list
}

type Program = | Program of MainProc * Proc list
