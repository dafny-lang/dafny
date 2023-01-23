// RUN: %exits-with 2 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Expr0 = Var(val: string)
               | Const(val: int)

datatype Expr1 = Var(val: seq<string>)
               | Const(val: seq<int>)

datatype Expr2 = Var(val: iset<string>)
               | Const(val: set<string>)

datatype Expr3 = Var(val: set<string>)
               | Const(val: iset<string>)
