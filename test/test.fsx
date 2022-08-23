module Test

open JanusInterpreter
open Computation
open AST
open Types


let prn' s x res = printfn "%s = %A is %b" s x res
let prn s x = printfn "# %s: %A" s x
let one = Int 1u

let res = evalBinOps Add one one
res = (Ok (Int 2u)) |> prn' "Ok (Int 2u)" res
evalBinOps Add (Int 0u) (Int 1u) |> prn ""
evalBinOps Add (Int 1u) (Int 1u) |> prn ""
evalBinOps Div (Int 1u) (Int 0u) |> prn ""
evalBinOps Div (Int 5u) (Int 2u) |> prn ""
evalBinOps Mod (Int 5u) (Int 0u) |> prn ""
evalBinOps LogAnd True True |> prn ""
evalBinOps LogAnd True False |> prn ""
evalBinOps LogOr True True |> prn ""
evalBinOps LogOr False False |> prn ""
evalBinOps LogOr (Int 1u) False |> prn ""
evalBinOps BitOr (Int 1u) (Int 1u) |> prn ""
evalBinOps BitOr (Int 0u) (Int 0u) |> prn ""
evalBinOps BitOr (Int 1u) (Int 0u) |> prn ""
evalBinOps BitAnd (Int 3u) (Int 3u) |> prn ""
evalBinOps BitAnd (Int 3u) (Int 1u) |> prn ""
evalBinOps BitAnd (Int 3u) (Int 0u) |> prn ""
evalBinOps BitAnd (Int 3u) False |> prn ""

printfn "\nEVAL EXPRESSIONS\n"

let env = (Map.ofList [], Map.ofList [])
let rt = evalExp (UnaryOp (Not, Const True)) env
let rf = evalExp (UnaryOp (Not, Const False)) env
let n = evalExp (UnaryOp (Not, Const (Int 1u))) env
prn "" <| rt
prn "" <| rf
prn "" <| n
evalExp (Const True) env |> prn ""

evalExp (BinOp (Add, Const (Int 2u), Const (Int 4u))) env |> prn "2 + 4"

let env' = (Map.ofList [], Map.empty |> Map.add "x" (Val (Int 4u)))

evalExp (BinOp (Add, Const (Int 2u), LVal (Var "x"))) env' |> prn "2 + x"
evalExp (BinOp (Add, Const (Int 2u), LVal (Var "y"))) env' |> prn "2 + y"
evalExp (BinOp (Add, LVal (Var "x"), LVal (Var "x"))) env' |> prn "x + x"

let envA = (Map.empty, Map.ofList [("arr", Arr [|True; False|]) ] )
evalExp (LVal (Lookup ("arr", Const (Int 1u)))) envA |> prn "arr[1] is False"

let vds = [
    Scalar ("t", True);
    Scalar ("x", Int 0u);
    Scalar ("z", Int 0u);
    Array ("a", 4)
]

run (execute (MainProc (vds , []))) env |> prn "Declare variables in Main"

let procs = [ {name = "p"; vdecls = [Scalar ("y", Int 4u)]; stmts = [] } ]
let prog = Program ((MainProc (vds, [])), procs)
runProgram prog |> prn "Declare variables in main and procedure p"

let upAddx11 = Assign (AddEq, Var "x", Const (Int 11u))
let progAdd = Program ((MainProc (vds, [upAddx11; upAddx11])), [])
runProgram progAdd |> prn "x += 11; x += 11"

let upAddE = Assign (AddEq, Var "x", Const (True))
let progAddE = Program ((MainProc (vds, [upAddE])), [])
runProgram progAddE |> prn "Error: x += True"


let vdeclA = [Array ("a", 4)]
let ai2v11 = Assign (AddEq, Lookup ("a", Const (Int 2u)), Const (Int 11u))
let pAddArr = Program ((MainProc (vdeclA, [ai2v11])), [])
runProgram pAddArr |> prn "a[2] += 11"

let ai2v7 = Assign (AddEq, Lookup ("a", Const (Int 2u)), Const (Int 7u))
let pAddArr2 = Program ((MainProc (vdeclA, [ai2v11; ai2v7; ai2v11])), [])
runProgram pAddArr2 |> prn "a[2] += 11; a[2] += 7; a[2] += 11;"

let ai3v7 = Assign (AddEq, Lookup ("a", Const (Int 3u)), Const (Int 7u))
let paa3 = Program ((MainProc (vdeclA, [ai2v11; ai2v7; ai3v7])), [])
runProgram paa3 |> prn "a[2] += 11; a[2] += 7; a[3] += 7;"

let s0v8 = Assign (SubEq, Lookup ("a", Const (Int 0u)), Const (Int 8u))
let s2v8 = Assign (SubEq, Lookup ("a", Const (Int 2u)), Const (Int 8u))
let pSub = Program ((MainProc (vdeclA, [ai2v11; s2v8])), [])
runProgram pSub |> prn "a[2] += 11; a[2] -= 8;"

let ai2i2 = Assign (AddEq, Lookup ("a", Const (Int 2u)), LVal (Lookup ("a", Const (Int 2u))))
let pUpA = Program ((MainProc (vdeclA, [ai2v11; ai2i2])), [])
runProgram pUpA |> prn "a[2] += 11; a[2] += a[2];"

let ai3v8 = Assign (AddEq, Lookup ("a", LVal (Var "x")), Const (Int 8u))
let pAx = Program ((MainProc (vds, [ai3v8])), [])
runProgram pAx |> prn "a[x] += 8;"

printfn "\nSWAP\n"

let xtswap = Assign (Swap, Var "x", LVal (Var "t"))
let pSwapVarVar = Program ((MainProc (vds, [xtswap])), [])
runProgram pSwapVarVar  |> prn "x <=> t;"

let xzswap = Assign (Swap, Var "x", LVal (Var "z"))
let pSwapVarVar' = Program ((MainProc (vds, [xzswap])), [])
runProgram pSwapVarVar'  |> prn "x <=> z;"

let xaswap = Assign (Swap, Var "x", LVal (Lookup ("a", Const (Int 2u))))
let pSwapVarA = Program ((MainProc (vds, [ai2v11; xaswap])), [])
runProgram pSwapVarA |> prn "x <=> a[2];"

let ai2i2swap = Assign (Swap, Lookup ("a", Const (Int 2u)), LVal (Lookup ("a", Const (Int 2u))))
let pSwap = Program ((MainProc (vdeclA, [ai2i2swap])), procs)
runProgram pSwap  |> prn "Swap w/ itself: a[2] <=> a[2];"

let ai3v42 = Assign (AddEq, Lookup ("a", Const (Int 3u)), Const (Int 42u))
let ai2i3swap = Assign (Swap, Lookup ("a", Const (Int 2u)), LVal (Lookup ("a", Const (Int 3u))))
let pSwapi2i3 = Program ((MainProc (vdeclA, [ai2v11; ai3v42; ai2i3swap])), procs)
runProgram pSwapi2i3  |> prn "a[2] += 11; a[3] += 42; a[2] <=> a[3];"


printfn "\nFOR LOOP\n"

let vd = [
    Scalar ("x", Int 0u);
]

let upAddx42 = Assign (AddEq, Var "x", Const (Int 42u))
let ift  = If (Const True,  upAddx11, upAddx42, Const True)
let iftE = If (Const True,  upAddx11, upAddx42, Const False)
let iff  = If (Const False, upAddx11, upAddx42, Const False)
let iffE = If (Const False, upAddx11, upAddx42, Const True)
let pIfT = Program ((MainProc (vd, [ift])), [])
runProgram pIfT |> prn "if true then x += 11 else x += 42 fi true"

let pIfTE = Program ((MainProc (vd, [iftE])), [])
runProgram pIfTE |> prn "Error: if true then x += 11 else x += 42 fi false"

let pIfF = Program ((MainProc (vd, [iff])), [])
runProgram pIfF |> prn "if false then x += 11 else x += 42 fi false"

let pIfFE = Program ((MainProc (vd, [iffE])), [])
runProgram pIfFE |> prn "Error: if false then x += 11 else x += 42 fi true"


printfn "\nDO LOOP\n"

let dos1 = DoLoop (Const True, upAddx11, upAddx42, Const True) // only do s1
let pdos1 = Program ((MainProc (vd, [dos1])), [])
runProgram pdos1 |> prn "FROM true DO x += 11 LOOP x += 42 UNTIL true"

let dos1E = DoLoop (Const True, upAddx11, upAddx42, Const False)
let pdos1E = Program ((MainProc (vd, [dos1E])), [])
runProgram pdos1E |> prn "ERROR: FROM true DO x += 11 LOOP x += 42 UNTIL false"

let doE = DoLoop (Const False, upAddx11, upAddx42, Const False)
let pdoE = Program ((MainProc (vds, [doE])), [])
runProgram pdoE |> prn "ERROR: FROM false DO x += 11 LOOP x += 42 UNTIL false"

printfn "\n"
let vd_ismax = [
    Scalar ("i", Int 0u);
    Scalar ("s", Int 0u);
    Scalar ("max", Int 0u)
]

let add10Max  = Assign (AddEq, Var "max", Const (Int 6u))
let e1_iEq0   = BinOp (Eq, LVal (Var "i"), Const (Int 0u))
let e2_sGtMax = BinOp (GEq, LVal (Var "s"), LVal (Var "max"))
let s1 = Assign (AddEq, Var "i", Const (Int 1u))
let s2 = Assign (AddEq, Var "s", LVal (Var "i"))
let doLoop = DoLoop (e1_iEq0, s1, s2, e2_sGtMax)
let pdoFull = Program ((MainProc (vd_ismax, [add10Max; doLoop])), [])
runProgram pdoFull |> prn "int i; int s; int max = 10;\n# FROM i=0 DO s += 1 LOOP s += i UNTIL s >= max;"

printfn "\nCALL\n"
let procsAdd = [ {name = "p"; vdecls = [Scalar ("y", Int 0u)]; stmts = [upAddx11] } ]
let pCall = Program (MainProc (vd, [Call "p"]), procsAdd)
runProgram pCall |> prn "call p (procedure p = x += 11;)"

let pCall' = Program (MainProc (vd, [upAddx11; Call "p"]), procsAdd)
runProgram pCall' |> prn "x += 11; call p (procedure p = x += 11;)"

printfn "\nUNCALL\n"
let pUncall = Program (MainProc (vd, [upAddx11; Uncall "p"]), procsAdd)
runProgram pUncall |> prn "x += 11; Uncall p"

let add15s = Assign (AddEq, Var "s", Const (Int 6u))
let add6i  = Assign (AddEq, Var "i", Const (Int 4u))
let procLoop = [ {name = "pLoop"; vdecls = []; stmts = [doLoop] } ]
let pUncallMax = Program (MainProc (vd_ismax, [add10Max; add15s; add6i; Uncall "pLoop"]), procLoop)
runProgram pUncallMax |> prn "i += 5; s += 10; max += 10;\n# Uncall DoLoop"


let r = RecordD ("r",
                 [ Scalar ("y", Int 2u);
                   Array ("a", 4);
                   RecordD ("rinternal", [Scalar ("y", Int 0u)])
                 ])
let vdsrec = r::vds
let prec = Program (MainProc (vdsrec, []), [])
runProgram prec |> prn "Record with  record in: "

let addRecRecVar = Assign (AddEq, Rec ("r", (Rec ("rinternal", Var "y"))), Const (Int 10u))
let precAdd = Program (MainProc (vdsrec, [addRecRecVar]), [])
runProgram precAdd |> prn "r.rinternal.y += 10;"

let procRec = [ {name = "p"; vdecls = []; stmts = [addRecRecVar] } ]
let pUncallRec = Program (MainProc (vdsrec, [Call "p"; Uncall "p"]), procRec)
runProgram pUncallRec
|> prn "(procedure p = r.rinternal.y += 10u); call p; uncall p;"

