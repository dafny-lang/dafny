// RUN: %dafny /compile:0 /rprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Value = Res(addr: nat) | Nil()

datatype Expr = Some(body: Expr)
              | None()

function f(e: Expr, fuel: nat): Value
    decreases fuel, 3
{
    var ret := Eval(e, fuel);
    Res(0)
}

function Eval(e: Expr, fuel: nat): Value
    decreases fuel, 0
{
    if fuel == 0 then Nil() else
    var fuel' := fuel - 1;
    match e
    case Some(body) => f(e.body, fuel')
    case None() => Nil()
}
const ctxp := Eval(None(), 1)
