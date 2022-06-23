module JanusInterpreter
open JanusAST

(* Define types of Procedure and variable environments/stores *)
//type ProcEnv = (ProcName * (Stmt list)) list
type Storetype =
    | Val of Value
    | Arr of Value array
    | Record of VarEnv
and VarEnv   = Map<VarName, Storetype> // Value>

type ProcEnv = Map<ProcName, Proc> //Stmt list>
type Env     = ProcEnv * VarEnv
let initPartEnv = Map.empty

type LValue' = // evalLValue to check there is only integers for array lookups
    | Var' of VarName
    | Lookup' of VarName * int
    | Rec' of VarName * LValue'

type RunError =
    | ErrVarName of VarName
    | ErrProcName of ProcName
    | ErrIndexOutOfRange of VarName * int
    | ErrConditional of string
    | ErrArg of string

module Computation =
    // Computation: Reader/ monad with value of Result tupled with store (:= VarEnv)
    type Comp<'a> = ((ProcEnv * VarEnv) -> (Result<'a, RunError> * VarEnv))

    let run (m : Comp<'a>) env = m env //Result<'a, RunError> * VarEnv>) env = m env
    let ret (x : 'a) = fun (_, varEnv) -> (Ok x, varEnv)
    let bind (m : Comp<'a>) (f : 'a -> Comp<'b>) : Comp<'b> =
        fun (procEnv, varEnv) ->
            match run m (procEnv, varEnv) with // run m in env to get monadic value
            | (Error err, _) -> (Error err, varEnv) // Error: return unchanged varEnv
            | (Ok res, varEnv) -> // Success: run (f res) in env to get final result
                let (res', varEnv') = run (f res) (procEnv, varEnv)
                in (res', varEnv')
    let (>>=) = bind

    let ask : Comp<Env> = fun (penv, venv) -> (Ok (penv, venv), venv)
    let put (venv : VarEnv) : Comp<unit> = fun _ ->  (Ok (), venv)
    let get : Comp<VarEnv> = fun (_, venv) -> (Ok venv, venv)
    let sequence (c1 : Comp<unit>) (c2: Comp<'a>) : Comp<'a> = c1 >>= fun _ -> c2
    let ( *>) = sequence

    let signalError (re : RunError) : Comp<'a> =
        fun (_, varEnv) -> (Error re, varEnv)

    let rec lookup (lv: LValue') (varEnv: VarEnv) : Result<Value, RunError> =
        match lv with
        | Var' vname ->
            match Map.tryFind vname varEnv with
            | Some (Val value) -> Ok value
            | _ -> Error <| ErrVarName vname
        | Lookup' (aname, index) ->
            match Map.tryFind aname varEnv with
            | Some (Arr arr) ->
                if 0 <= index && index < arr.Length
                then Ok arr.[index]
                else Error <| ErrIndexOutOfRange (aname,index)
            | _ -> Error <| ErrVarName aname
        | Rec' (rname, lv') ->
            match Map.tryFind rname varEnv with
            | Some (Record recEnv) -> lookup lv' recEnv
            | _ -> Error <| ErrVarName rname

    let lookupVar (lv: LValue') : Comp<Value> =
        fun (procEnv, varEnv) ->
            let res = lookup lv varEnv
            in res, varEnv

//    let lookupVar (vname : VarName) (index : int option) : Comp<Value> =
//        fun (_procEnv, varEnv) ->
//            let res =
//                match Map.tryFind vname varEnv with
//                | Some (Val value) -> Ok value
//                | Some (Arr arr) ->
//                    let index = Option.get index in
//                    if 0 <= index && index < arr.Length
//                    then Ok arr.[index]
//                    else Error <| ErrIndexOutOfRange (vname,index)
//                | _ -> Error <| ErrVarName vname
//            in res, varEnv

    let lookupProc (pname : ProcName) : Comp<Proc> =
        fun (procEnv, varEnv) ->
            let res =
                match Map.tryFind pname procEnv with
                | Some p -> Ok p
                | None -> Error <| ErrProcName pname
            in res, varEnv

    type ComputationBuilder() =
        member this.Return(x) = ret x
        member this.ReturnFrom(m) = m
        member this.Bind(m, f) = m >>= f
        member this.Zero() = Map.ofList []
    let Comp = new ComputationBuilder()

open Computation
type ErrorMsg = string

let getTruth (value : Value) : bool =
    match value with
    | Int 0 -> false
    | False -> false
    | _     -> true  // True is true and all integers != 0 are true

let evalBinOps (op : BinOp) (v1 : Value) (v2 : Value) : Result<Value,ErrorMsg> =
    match op, v1, v2 with
    | Add, (Int v1), (Int v2) -> Ok <| Int (v1 + v2)
    | Sub, (Int v1), (Int v2) -> Ok <| Int (v1 - v2)
    | Mul, (Int v1), (Int v2) -> Ok <| Int (v1 * v2)
    | Div, (Int v1), (Int v2) ->
        if v2 = 0
        then Error "Division by 0 is undefined"
        else Ok <| Int (v1 / v2)
    | Mod, (Int v1), (Int v2) ->
        if v2 = 0
        then Error "Modulo by 0 is undefined"
        else Ok <| Int (v1 % v2)
    | Gt,  (Int v1), (Int v2) -> Ok <| if v1 > v2 then True else False
    | Lt,  (Int v1), (Int v2) -> Ok <| if v1 < v2 then True else False
    | Eq,  (Int v1), (Int v2) -> Ok <| if v1 = v2 then True else False
    | NEq, (Int v1), (Int v2) -> Ok <| if v1 <> v2 then True else False
    | GEq, (Int v1), (Int v2) -> Ok <| if v1 >= v2 then True else False
    | LEq, (Int v1), (Int v2) -> Ok <| if v1 <= v2 then True else False
    | BitAnd, (Int v1),  (Int v2) -> Ok <| Int (v1 &&& v2)
    | BitOr,  (Int v1),  (Int v2) -> Ok <| Int (v1 ||| v2)
    | Xor,    (Int v1),  (Int v2) -> Ok <| Int (v1 ^^^ v2)
    | LogAnd, True,  True  -> Ok True
    | LogAnd, _,     _     -> Ok False
    | LogOr,  False, False -> Ok False
    | LogOr,  _,     _     -> Ok True
    | op, v1, v2 -> Error <| sprintf "Unvalid operation: (%A) %A (%A)" v1 op v2

let rec evalExp (ex : Exp) : Comp<Value> =
    match ex with
    | Const v -> Comp { return v }
    | LVal lv -> evalLVal lv
    | UnaryOp (Not, ex') ->
        evalExp ex' >>= function
            | True  -> Comp { return False }
            | False -> Comp { return True }
            | _ -> signalError <| ErrArg "Not a bool value"
    | BinOp (bOp, ex1, ex2) ->
        Comp {
            let! v1 = evalExp ex1
            let! v2 = evalExp ex2
            match evalBinOps bOp v1 v2 with
            | Ok value -> return value
            | Error err -> return! signalError <| ErrArg err }

and evalLVal lv =
    constructlv' lv >>= fun lv' ->
        lookupVar lv'

and constructlv' (lv : LValue) : Comp<LValue'> =
    match lv with
    | Var vname -> Comp { return Var' vname }
    | Lookup (aname, ex) ->
        evalExp ex >>= function
            | Int index -> Comp { return Lookup' (aname, index) }
            | _ -> signalError <| ErrArg "Not an index for arrays"
    | Rec (rname, rlv) ->
        constructlv' rlv >>= fun lv' ->
            Comp { return Rec' (rname, lv') }
//    | Var v -> lookupVar v None
//    | Lookup (vname, ex) ->
//        evalExp ex >>= function
//            | Int index ->
//                lookupVar vname (Some index)
//            | _ -> signalError <| ErrArg "Not an index for array"
//    | Rec (rname, lv) ->
//        // 1. fra lv til lv' uden expressions
//        // 2. recursivt lookup med lv'
//        lookupVar lv'

let rec declare (vd : VDec) (varEnv : VarEnv) : VarEnv = // Result<VarEnv, RunError> =
    match vd with
    | Scalar (vname, value) ->
        let varEnv' = Map.add vname (Val value) varEnv
        in varEnv'
    | Array (aname, size) ->
         let initArray s = Array.create s (Int 0)
         let varEnv' = Map.add aname (Arr (initArray size)) varEnv
         in varEnv'
    | RecordD (rname, vds) ->
        let recEnv = Map.empty<VarName,Storetype>
        let recEnv' = List.fold (fun venv vd -> declare vd venv) recEnv vds
        let varEnv' = Map.add rname (Record recEnv') varEnv
        in varEnv'

let declareVarsInStore (vd : VDec) : Comp<unit> =
        get >>= fun varEnv ->
        let varEnv' = declare vd varEnv
        put varEnv'


let rec update (lv' : LValue') (value : Value) (varEnv : VarEnv) : Result<VarEnv, RunError> =
    match lv' with
    | Var' vname ->
        let varEnv' = Map.add vname (Val value) varEnv
        in Ok varEnv'

    | Lookup' (aname, index) ->
        match Map.tryFind aname varEnv with
        | Some (Arr arr) ->
            if 0 <= index && index < arr.Length
            then arr.[index] <- value
                 Ok varEnv
            else Error <| ErrIndexOutOfRange (aname, index)
        | _ -> Error <| ErrVarName aname

    | Rec' (rname, lv'') ->
        match Map.tryFind rname varEnv with
        | Some (Record recEnv) ->
            let recEnv' = update lv'' value recEnv
            match recEnv' with
            | Ok recEnv' ->
                let varEnv' = Map.add rname (Record recEnv') varEnv
                in Ok varEnv'
            | err -> err
        | _ -> Error <| ErrVarName rname

let updateStore (lv' : LValue') (v : Value) : Comp<unit> =
        get >>= fun varEnv ->
        match update lv' v varEnv with
        | Ok varEnv' -> put varEnv'
        | Error err -> signalError <| err

//let updateStore (vname: VarName) (v: Value option) (index: int option) (comp: Comp<unit>) : Comp<unit> =
//    fun (procEnv, varEnv) ->
//        match index with
//        | Some index ->
//            match v with
//            | None -> // initialize an array variable in store
//                let initArray size = Array.create size (Int 0)
//                let varEnv' = Map.add vname (Arr (initArray index)) varEnv
//                in run comp (procEnv, varEnv')
//            | Some value -> // update an array variable in store at specific index
//                match Map.tryFind vname varEnv with
//                | Some (Arr arr) ->
//                    if 0 <= index && index < arr.Length
//                    then arr.[index] <- value; run comp (procEnv, varEnv)
//                    else let err = Error <| ErrIndexOutOfRange (vname, index)
//                         in err, varEnv
//                | _ -> let err = Error <| ErrVarName vname in err, varEnv
//        | None -> // update or initialize a Value variable in store
//            let value = Option.get v in
//            let varEnv' = Map.add vname (Val value) varEnv
//            in run comp (procEnv, varEnv')

let updateOpToBinOp (upOp : UpdateOp) : BinOp = if upOp = AddEq then Add else Sub

let getIndex (lv: LValue) : Comp<int option> =
    fun (procEnv, varEnv) ->
        let index =
            match lv with
            | Lookup (_, e) ->
                match run (evalExp e) (procEnv,varEnv) with
                | Ok (Int i),_ -> Ok <| Some i
                | Error err,_ -> Error <| err
                | _ -> Error <| ErrArg "Not an index for arrays"
            | Var _ -> Ok None
            | Rec _ -> Ok None
        in (index, varEnv)

let getVarName = function
    | Var vname -> vname
    | Lookup (vname,_) -> vname
    | Rec (rname,_) -> rname

let rec invert = function
    | Assign (AddEq, lv, e) -> Assign (SubEq, lv, e)
    | Assign (SubEq, lv, e) -> Assign (AddEq, lv, e)
    | Assign (Swap,  lv, e) -> Assign (Swap, lv, e)
    | If (test, s1, s2, assertion) ->
        If (assertion, invert s1, invert s2, test)
    | DoLoop (test, s1, s2, assertion) ->
        DoLoop (assertion, invert s1, invert s2, test)
    | Call procName -> Uncall procName
    | Uncall procName -> Call procName
    | Skip -> Skip
    | Sequence ss ->
        List.rev ss
        |> List.map invert
        |> Sequence

let rec evalStmts (stmts : Stmt list) : Comp<unit> =
    match stmts with
    | [] -> Comp { return () }
    | s::ss ->
        match s with
        | Assign (Swap, (var1 : LValue), LVal (var2 : LValue)) -> // (<=>)
            constructlv' var1 >>= fun var1' ->
            constructlv' var2 >>= fun var2' ->
            lookupVar var1' >>= fun value1 ->
            lookupVar var2' >>= fun value2 ->
            let vname1 = getVarName var1
            let vname2 = getVarName var2
            getIndex var1 >>= fun i1 ->
            getIndex var2 >>= fun i2 ->
         // lookupVar vname1 i1 >>= fun value1 ->
         // lookupVar vname2 i2 >>= fun value2 ->
//          updateStore vname1 (Some value2) i1 *> //>>= fun _ ->
//          updateStore vname2 (Some value1) i2 *> //>>= fun _ ->
         // <| evalStmts ss
            updateStore var1' value2 *>
            updateStore var2' value1 *>
            evalStmts ss
        | Assign (Swap, _, _) -> signalError <| ErrArg "Can only swap variables"
        | Assign (updateOp, lv, e) -> // (+) (-)
            evalLVal lv >>= fun v1 ->
            evalExp e >>= fun v2 ->
            let binOp = updateOpToBinOp updateOp
            match evalBinOps binOp v1 v2 with
            | Error err -> signalError <| ErrArg err
            | Ok newVal ->
                constructlv' lv >>= fun v1' ->
                updateStore v1' newVal *>
                evalStmts ss
               // let vname = getVarName lv
               // getIndex lv >>= fun index ->
               // updateStore vname (Some newVal) index  *> //>>= fun _ ->
                // <| evalStmts ss
        | If (e1, s1, s2, e2) -> Comp {
            let! test = evalExp e1
            if getTruth test
            then do! evalStmts [s1]
                 let! assertion = evalExp e2
                 if getTruth assertion
                 then return! evalStmts ss
                 else return! signalError <| ErrConditional "Assertion in if-statement should be True"
            else do! evalStmts [s2]
                 let! assertion = evalExp e2
                 if getTruth assertion
                 then return! signalError <| ErrConditional "Assertion in if-statement should be False"
                 else return! evalStmts ss
            }
        | DoLoop (e1, s1, s2, e2) ->
            evalExp e1 >>= fun test ->
            if not (getTruth test)
            then signalError <| ErrConditional "Entry test in do loop is false"
            else
                evalStmts [s1] >>= fun _ ->

                let rec doWhile s1 s2 e2 e1 =
                    evalExp e2 >>= fun assertion ->
                    if not <| getTruth assertion
                    then evalStmts [s2] >>= fun _ ->
                         evalExp e1 >>= fun test' ->
                         if not <| getTruth test'
                         then evalStmts [s1] >>= fun _ -> doWhile s1 s2 e2 e1
                         else signalError <| ErrConditional "Test in do loop is true after entry"
                    else evalStmts ss

                doWhile s1 s2 e2 e1
        | Call procName ->
            lookupProc procName >>= fun proc ->
            execute' proc.stmts proc.vdecls >>= fun _ ->
            evalStmts ss

        | Uncall procName ->
            lookupProc procName >>= fun proc ->
            let invertedStmts =
                List.rev proc.stmts
                |> List.map invert
            execute' invertedStmts proc.vdecls >>= fun _ ->
            evalStmts ss

        | Skip -> Comp { return () }
        | Sequence ss -> evalStmts ss

and execute' stmts = function
    | [] -> evalStmts stmts
    | vd::vds -> declareVarsInStore vd *> execute' stmts vds

//and execute' stmts = function
//    | [] -> evalStmts stmts
//    | Scalar (vname, value)::vds ->
//        updateStore vname (Some value) None <| execute' stmts vds
//    | Array (vname, size)::vds ->
//        updateStore vname None (Some size) <| execute' stmts vds
//    | RecordD (rname, vds) ->
//        updateStore

let execute (MainProc (vardecls, stmts) : MainProc) : Comp<_> =
    execute' stmts vardecls

let initProcedureEnv procs : Result<ProcEnv, RunError> =
    let rec init env = function
        | [] -> Ok env
        | p::ps ->
            if Map.containsKey p.name env
            then Error <| ErrArg "Duplicate procedure names"
            else let env' = Map.add p.name p env in init env' ps //Check dup idents
    init initPartEnv procs

let runProgram (Program (main, procs) : Program) = //: (RunError option * VarEnv) =
        match initProcedureEnv procs with
        | Ok procEnv ->
            let env = (procEnv, initPartEnv) in
        //    printfn "\nenv: %A\n" env
            match run (execute main) env with // get monadic value
            | (Ok _,  store) -> (None, store |> Map.toList)
            | (Error err, store) -> (Some err, store |> Map.toList)
        | Error err -> (Some err, initPartEnv |> Map.toList)


