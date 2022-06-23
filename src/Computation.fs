module Computation
open Types

// Computation: Reader/State monad with value being a Result tupled with store (:= VarEnv)
type Comp<'a> = ((ProcEnv * VarEnv) -> (Result<'a, RunError> * VarEnv))

(* Run m in env to get monadic value *)
let run (m : Comp<'a>)
        (env : ProcEnv * VarEnv)
        : Result<'a, RunError> * VarEnv =
    m env

let ret (x : 'a) = fun (_, varEnv) -> (Ok x, varEnv)

let bind (m : Comp<'a>)
         (f : 'a -> Comp<'b>)
         : Comp<'b> =
    fun ((procEnv, varEnv) as env) ->
        // run m in env to get monadic value
        match run m env with
        // Error: return unchanged varEnv
        | (Error err, _) -> (Error err, varEnv)
        // Success: Now run (f res) in env to get final result
        | (Ok res, varEnv') ->
            let (res', varEnv'') = run (f res) (procEnv, varEnv')
            in (res', varEnv'')

let (>>=) = bind

let ask : Comp<Env> = fun (penv, venv) -> (Ok (penv, venv), venv)

let put (venv : VarEnv) : Comp<unit> = fun _ ->  (Ok (), venv)

let get : Comp<VarEnv> = fun (_, venv) -> (Ok venv, venv)

let sequence (c1 : Comp<unit>) (c2: Comp<'a>) : Comp<'a> =
    c1 >>= fun _ -> c2

let ( *>) = sequence

let signalError (re : RunError) : Comp<'a> =
    fun (_, varEnv) -> (Error re, varEnv)

type ComputationBuilder() =
    member this.Return(x) = ret x
    member this.ReturnFrom(m) = m
    member this.Bind(m, f) = m >>= f
    member this.Zero() = Map.ofList []

let Comp = new ComputationBuilder()

