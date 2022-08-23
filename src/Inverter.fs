module Inverter

module StatementInverter =
    open Types
    open AST

    let rec invertStmt (stmt : Stmt) : Stmt =
        match stmt with
        | Assign (AddEq, lv, e) -> Assign (SubEq, lv, e)
        | Assign (SubEq, lv, e) -> Assign (AddEq, lv, e)
        | Assign (Swap,  lv, e) -> Assign (Swap, lv, e)
        | If (test, s1, s2, assertion) ->
            If (assertion, invertStmt s1, invertStmt s2, test)
        | DoLoop (test, s1, s2, assertion) ->
            DoLoop (assertion, invertStmt s1, invertStmt s2, test)
        | Call procName -> Uncall procName
        | Uncall procName -> Call procName
        | Skip -> Skip
        | Sequence ss ->
            List.rev ss
            |> List.map invertStmt
            |> Sequence

    let invert (stmts : Stmt list) : Stmt list =
        List.rev stmts
        |> List.map invertStmt

