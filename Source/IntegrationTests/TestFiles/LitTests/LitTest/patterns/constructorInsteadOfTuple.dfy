// RUN: ! %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Expr =
    | Const(value: int)
    | Var(name: string)
    | Add(left: Expr, right: Expr)
    | Mult(left: Expr, right: Expr)

function Optimize(expr: Expr): Expr
{
    match expr
        case Const(value) => Const(value)
        case Var(name) => Var(name)
        case Add(left, right) =>
            match (Optimize(left), Optimize(right))
                case (Const(lv), Const(rv)) => Const(lv + rv)
                case (Const(0), rv) => rv
                case (lv, Const(0)) => lv
                case (lv, rv) => Add(lv, rv)
                case Mult(left, right) =>
                    match (Optimize(left), Optimize(right))
                        case (Const(lv), Const(rv)) => Const(lv * rv)
                        case (Const(0), _) => Const(0)
                        case (_, Const(0)) => Const(0)
                        case (Const(1), rv) => rv
                        case (lv, Const(1)) => lv
                        case (lv, rv) => Mult(lv, rv)
}