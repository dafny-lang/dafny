// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function foo(s:int) : (int, int)

function bar(s:int) : bool
{
    var (x, rest) := foo(s);
    x > 0
}
