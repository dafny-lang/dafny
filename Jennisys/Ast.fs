namespace Ast
open System

type Expr =
  | IdLiteral of string
  | Dot of Expr * string
  | BinExpr of string * Expr * Expr

