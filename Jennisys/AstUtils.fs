module AstUtils

open Ast

let BinaryAnd (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> rhs
    | IdLiteral("false"), _ -> IdLiteral("false")
    | _, IdLiteral("true")  -> lhs
    | _, IdLiteral("false") -> IdLiteral("false")
    | _, _                  -> BinaryExpr(30, "&&", lhs, rhs)

let BinaryOr (lhs: Expr) (rhs: Expr) = 
    match lhs, rhs with
    | IdLiteral("true"), _  -> IdLiteral("true")
    | IdLiteral("false"), _ -> rhs
    | _, IdLiteral("true")  -> IdLiteral("true")
    | _, IdLiteral("false") -> lhs
    | _, _                  -> BinaryExpr(30, "||", lhs, rhs)

let BinaryImplies lhs rhs = BinaryExpr(20, "==>", lhs, rhs)

let BinaryNeq lhs rhs = BinaryExpr(40, "!=", lhs, rhs)

let TrueLiteral = IdLiteral("true")
let FalseLiteral = IdLiteral("false")