// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T(n:int)
ghost function P(x: int) : int { x - 1}

ghost function ToInt(t:T) : int
 ensures ToInt(t) == t.n as int;
 {
    t.n as int
 }

method Test(x:int)
 {
    assume exists p:int :: exists t:T :: ToInt(t) > 0;
    assert exists p:int :: exists t:T :: ToInt(t) > 0;
 }




