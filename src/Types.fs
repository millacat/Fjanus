module Types
open AST

type Storetype =
    | Val of Value
    | Arr of Value array
    | Record of VarEnv
and VarEnv   = Map<VarName, Storetype>

type ProcEnv = Map<ProcName, Proc>
type Env     = ProcEnv * VarEnv

type LValue' = // ensure only integers for array lookups
    | Var' of VarName
    | Lookup' of VarName * int
    | Rec' of VarName * LValue'

type ErrorMsg = string

type RunError =
    | ErrVarName of VarName
    | ErrProcName of ProcName
    | ErrIndexOutOfRange of VarName * int
    | ErrConditional of ErrorMsg
    | ErrArg of ErrorMsg

