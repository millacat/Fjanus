module Inverter

module StatementInverter =
    open Types
    open AST

    let rec invert (stmt : Stmt) : Stmt =
        match stmt with
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



