module test

open JanusInterpreter
open JanusAST
open JanusInterpreter.Computation


let prn' s x res = printfn "%s = %A is %b" s x res
let prn s x = printfn "%s: %A" s x
let one = Int 1

let res = evalBinOps Add one one
res = (Ok (Int 2)) |> prn' "Ok (Int 2)" res
evalBinOps Add (Int 0) (Int 1) |> prn ""
evalBinOps Add (Int -1) (Int 1) |> prn ""
evalBinOps Div (Int 1) (Int 0) |> prn ""
evalBinOps Div (Int 5) (Int 2) |> prn ""
evalBinOps Mod (Int 5) (Int 0) |> prn ""
evalBinOps LogAnd True True |> prn ""
evalBinOps LogAnd True False |> prn ""
evalBinOps LogOr True True |> prn ""
evalBinOps LogOr False False |> prn ""
evalBinOps LogOr (Int 1) False |> prn ""
evalBinOps BitOr (Int 1) (Int 1) |> prn ""
evalBinOps BitOr (Int 0) (Int 0) |> prn ""
evalBinOps BitOr (Int 1) (Int 0) |> prn ""
evalBinOps BitAnd (Int 3) (Int 3) |> prn ""
evalBinOps BitAnd (Int 3) (Int 1) |> prn ""
evalBinOps BitAnd (Int 3) (Int 0) |> prn ""
evalBinOps BitAnd (Int 3) False |> prn ""

let env = (Map.ofList [], Map.ofList [])
let rt = evalExp (UnaryOp (Not, Const True)) env
let rf = evalExp (UnaryOp (Not, Const False)) env
let n = evalExp (UnaryOp (Not, Const (Int 1))) env
prn "" <| rt
prn "" <| rf
prn "" <| n
evalExp (Const True) env |> prn ""
evalExp (BinOp (Add, Const (Int 2), Const (Int 4))) env |> prn "2 + 4: "

//let env' = (Map.ofList [], Map.empty |> Map.add "x" (Val (Int 4)))

//evalExp (BinOp (Add, Const (Int 2), LVal (Var "x"))) env' |> prn "2 + x: "
//evalExp (BinOp (Add, Const (Int 2), LVal (Var "y"))) env' |> prn "2 + y: "
//evalExp (BinOp (Add, LVal (Var "x"), LVal (Var "x"))) env' |> prn "x + x: "
//
//let envA = (Map.empty, Map.ofList [("arr", Arr [|True; False|]) ] )
//evalExp (LVal (Lookup ("arr", Const (Int 1)))) envA |> prn "LVal"
//
let vds = [
    Scalar ("t", True);
    Scalar ("x", Int 3);
    Scalar ("z", Int 1);
    Array ("a", 4)
]

//run (execute (MainProc ([Array ("a", 4)], []))) env |> prn ""
//run (execute (MainProc (vds , []))) env |> prn ""
//
//let procs = [ {name = "p1"; vdecls = [Scalar ("y", Int 4)]; stmts = [] } ]
//let prog = Program ((MainProc (vds, [])), procs)
//runProgram prog |> prn ""
//
let upAddx11 = Assign (AddEq, Var "x", Const (Int 11))
//let progAdd = Program ((MainProc (vds, [upAddx11; upAddx11])), [])
//runProgram progAdd |> prn ""
//
//let upAddE = Assign (AddEq, Var "x", Const (True))
//let progAddE = Program ((MainProc (vds, [upAddE])), [])
//runProgram progAddE |> prn "x += True"
//
//
//let vdeclA = [Array ("a", 4)]
//let ai2v11 = Assign (AddEq, Lookup ("a", Const (Int 2)), Const (Int 11))
//let pAddArr = Program ((MainProc (vdeclA, [ai2v11])), [])
//runProgram pAddArr |> prn "a[2] += 11\n"
//
//let AddArr2 = Assign (AddEq, Lookup ("a", Const (Int 2)), Const (Int 7))
//let pAddArr2 = Program ((MainProc (vdeclA, [ai2v11; AddArr2; ai2v11])), [])
//runProgram pAddArr2 |> prn "a[2] += 11; a[2] += 7; a[2] += 11\n"
//
//let AddArrI3 = Assign (AddEq, Lookup ("a", Const (Int 3)), Const (Int 7))
//let pAddArr3 = Program ((MainProc (vdeclA, [ai2v11; AddArr2; AddArrI3])), [])
//runProgram pAddArr3 |> prn "a[2] += 11; a[2] += 7; a[3] += 7\n"
//
//let s0v8 = Assign (SubEq, Lookup ("a", Const (Int 0)), Const (Int 8))
//let s2v8 = Assign (SubEq, Lookup ("a", Const (Int 2)), Const (Int 8))
//let pSub = Program ((MainProc (vdeclA, [ai2v11; s2v8])), procs)
//runProgram pSub |> prn "a[2] += 11; a[2] -= 8;\n"
//
//let ai2i2 = Assign (AddEq, Lookup ("a", Const (Int 2)), LVal (Lookup ("a", Const (Int 2))))
//let pUpA = Program ((MainProc (vdeclA, [ai2v11; ai2i2])), procs)
//runProgram pUpA |> prn "a[2] += 11; a[2] += a[2];\n"
//
//let axtswap = Assign (Swap, Var "x", LVal (Var "t"))
//let pSwapVarVar = Program ((MainProc (vds, [axtswap])), procs)
//runProgram pSwapVarVar  |> prn "x <=> t\n"
//
//let xzswap = Assign (Swap, Var "x", LVal (Var "z"))
//let pSwapVarVar' = Program ((MainProc (vds, [xzswap])), procs)
//runProgram pSwapVarVar'  |> prn "x <=> z\n"
//
//let xaswap = Assign (Swap, Var "x", LVal (Lookup ("a", Const (Int 2))))
//let pSwapVarA = Program ((MainProc (vds, [ai2v11; xaswap])), procs)
//runProgram pSwapVarA |> prn "x <=> a[2]\n"
//
//
//let ai2swap = Assign (Swap, Lookup ("a", Const (Int 2)), LVal (Lookup ("a", Const (Int 2))))
//let pSwap = Program ((MainProc (vdeclA, [ai2swap])), procs)
//runProgram pSwap  |> prn "a[2] <=> a[2]\n"
//
//let ai3v42 = Assign (AddEq, Lookup ("a", Const (Int 3)), Const (Int 42))
//let ai2i3swap = Assign (Swap, Lookup ("a", Const (Int 2)), LVal (Lookup ("a", Const (Int 3))))
//let pSwapi2i3 = Program ((MainProc (vdeclA, [ai2v11; ai3v42; ai2i3swap])), procs)
//runProgram pSwapi2i3  |> prn "(a[2] += 11, a[3] += 42; a[2] <=> a[3]\n"
//
//
//let upAddx42 = Assign (AddEq, Var "x", Const (Int 42))
//let ift  = If (Const True, upAddx11, upAddx42, Const True)
//let iftE = If (Const True, upAddx11, upAddx42, Const False)
//let iff  = If (Const False, upAddx11, upAddx42, Const False)
//let iffE = If (Const False, upAddx11, upAddx42, Const True)
//let pIfT = Program ((MainProc (vds, [ift])), [])
//runProgram pIfT |> prn "\nif true then x += 11 else x += 42 fi true"
//
//let pIfTE = Program ((MainProc (vds, [iftE])), [])
//runProgram pIfTE |> prn "if true then x += 11 else x += 42 fi false"
//
//let pIfF = Program ((MainProc (vds, [iff])), [])
//runProgram pIfF |> prn "if false then x += 11 else x += 42 fi false"
//let pIfFE = Program ((MainProc (vds, [iffE])), [])
//runProgram pIfFE |> prn "if false then x += 11 else x += 42 fi true"
//
//
//let dos1 = DoLoop (Const True, upAddx11, upAddx42, Const True) // only do s1
//let pdos1 = Program ((MainProc (vds, [dos1])), [])
//runProgram pdos1 |> prn "\nFROM true DO x += 11 LOOP x += 42 UNTIL true"
//
//let dos1E = DoLoop (Const True, upAddx11, upAddx42, Const False)
//let pdos1E = Program ((MainProc (vds, [dos1E])), [])
//runProgram pdos1E |> prn "\nFROM true DO x += 11 LOOP x += 42 UNTIL false"
//
//let doE = DoLoop (Const False, upAddx11, upAddx42, Const False)
//let pdoE = Program ((MainProc (vds, [doE])), [])
//runProgram pdoE |> prn "\nFROM false DO x += 11 LOOP x += 42 UNTIL false"
//
printfn "\n\n"
let vd_ismax = [
    Scalar ("i", Int 0);
    Scalar ("s", Int 0);
    Scalar ("max", Int 0)
]

let add10Max  = Assign (AddEq, Var "max", Const (Int 10))
let e1_iEq0   = BinOp (Eq, LVal (Var "i"), Const (Int 0))
let e2_sGtMax = BinOp (GEq, LVal (Var "s"), LVal (Var "max"))
let s1 = Assign (AddEq, Var "i", Const (Int 1))
let s2 = Assign (AddEq, Var "s", LVal (Var "i"))
let doLoop = DoLoop (e1_iEq0, s1, s2, e2_sGtMax)
let pdoFull = Program ((MainProc (vd_ismax, [add10Max; doLoop])), [])
runProgram pdoFull |> prn "int i; int s; int max = 10; FROM i=0 DO s += 1 LOOP s += i UNTIL s > max\n"

let procsAdd = [ {name = "p"; vdecls = [Scalar ("y", Int 4)]; stmts = [upAddx11] } ]
let pCall = Program (MainProc (vds, [Call "p"; upAddx11]), procsAdd)
runProgram pCall |> prn "call p"

let pUncall = Program (MainProc (vds, [Uncall "p"]), procsAdd)
runProgram pUncall |> prn "Uncall p"

printfn "\n"
let add15s = Assign (AddEq, Var "s", Const (Int 10))
let add6i  = Assign (AddEq, Var "i", Const (Int 5))
let procLoop = [ {name = "pLoop"; vdecls = []; stmts = [doLoop] } ]
let pUncallMax = Program (MainProc (vd_ismax, [add10Max; add15s; add6i; Uncall "pLoop"]), procLoop)
runProgram pUncallMax |> prn "i += 5; s += 10; max += 10; Uncall DoLoop"

//printfn "\n### Initial variable declariations:\n%A" vds
