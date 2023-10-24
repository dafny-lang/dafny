// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function foo(s:int) : (int, int)

ghost function bar(s:int) : bool
{
    var (x, rest) := foo(s);
    x > 0
}