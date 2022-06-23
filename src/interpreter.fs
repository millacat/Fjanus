module JanusInterpreter

open AST
open Types
open Computation
open Inverter

(*############################################################################*)
(******************* Functions related to the environment *********************)
(*############################################################################*)
let rec declareVar (vd : VDec) (varEnv : VarEnv) : VarEnv =
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
        let recEnv' = List.fold (fun venv vd -> declareVar vd venv) recEnv vds
        let varEnv' = Map.add rname (Record recEnv') varEnv
        in varEnv'

let declareVarsInStore (vd : VDec) : Comp<unit> =
        get >>= fun varEnv ->
        let varEnv' = declareVar vd varEnv
        put varEnv'

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
    Comp { let! varEnv = get
           match lookup lv varEnv with
           | Ok r -> return r
           | Error err -> return! signalError err }

let lookupProc (pname : ProcName) : Comp<Proc> =
    ask >>=  fun (procEnv, varEnv) ->
    Comp { match Map.tryFind pname procEnv with
           | Some p -> return p
           | None -> return! signalError <| ErrProcName pname }

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
        | Error err -> signalError err


(*############################################################################*)
(******************************* Interpreter **********************************)
(*############################################################################*)


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
    | BitAnd, (Int v1), (Int v2) -> Ok <| Int (v1 &&& v2)
    | BitOr,  (Int v1), (Int v2) -> Ok <| Int (v1 ||| v2)
    | Xor,    (Int v1), (Int v2) -> Ok <| Int (v1 ^^^ v2)
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
        Comp {
            match! evalExp ex' with
            | True  -> return False
            | False -> return True
            | _ -> return! signalError <| ErrArg "Not a bool value" }
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

let upOpToBinOp (upOp : UpdateOp) : BinOp = if upOp = AddEq then Add else Sub

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


let rec evalStmts (stmts : Stmt list) : Comp<unit> =
    match stmts with
    | [] -> Comp { return () }
    | s::ss ->
        match s with
        | Assign (Swap, (var1 : LValue), LVal (var2 : LValue)) -> // (<=>) (^)
            constructlv' var1 >>= fun var1' ->
            constructlv' var2 >>= fun var2' ->
            lookupVar var1' >>= fun value1 ->
            lookupVar var2' >>= fun value2 ->
            updateStore var1' value2 *>
            updateStore var2' value1 *>
            evalStmts ss
        | Assign (Swap, _, _) -> signalError <| ErrArg "Can only swap variables"

        | Assign (updateOp, lv, e) -> // (+) (-)
            let binOp = upOpToBinOp updateOp
            evalLVal lv >>= fun v1 ->
            evalExp e >>= fun v2 ->
            match evalBinOps binOp v1 v2 with
            | Error err -> signalError <| ErrArg err
            | Ok newVal ->
                constructlv' lv >>= fun v1' ->
                updateStore v1' newVal *>
                evalStmts ss

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
                    if not (getTruth assertion)
                    then evalStmts [s2] >>= fun _ ->
                         evalExp e1 >>= fun test' ->
                         if not (getTruth test')
                         then evalStmts [s1] >>= fun _ -> doWhile s1 s2 e2 e1
                         else signalError <| ErrConditional "Test in do loop is true after entry"
                    else evalStmts ss

                doWhile s1 s2 e2 e1
        | Call procName ->
            lookupProc procName >>= fun proc ->
            execute' proc.stmts proc.vdecls *>
            evalStmts ss

        | Uncall procName ->
            lookupProc procName >>= fun proc ->
            let invertedStmts =
                List.rev proc.stmts
                |> List.map StatementInverter.invert
            execute' invertedStmts proc.vdecls *>
            evalStmts ss

        | Skip -> Comp { return () }
        | Sequence ss -> evalStmts ss

and execute' stmts = function
    | [] -> evalStmts stmts
    | vd::vds -> declareVarsInStore vd *> execute' stmts vds

let execute (MainProc (vardecls, stmts) : MainProc) : Comp<_> =
    execute' stmts vardecls

let initPartEnv = Map.empty

let initProcedureEnv procs : Result<ProcEnv, RunError> =
    let rec init env = function
        | [] -> Ok env
        | p::ps ->
            if Map.containsKey p.name env // Check dup identifiers
            then Error <| ErrArg "Duplicate procedure names"
            else let env' = Map.add p.name p env in init env' ps

    init initPartEnv procs

let runProgram (Program (main, procs) : Program) = //: (RunError option * VarEnv) =
        match initProcedureEnv procs with
        | Ok procEnv ->
            let env = (procEnv, initPartEnv) in
            match run (execute main) env with // get monadic value
            | (Ok _,  store) -> (None, store |> Map.toList)
            | (Error err, store) -> (Some err, store |> Map.toList)
        | Error err -> (Some err, initPartEnv |> Map.toList)

