// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T(n:int)
function P(x: int) : int { x - 1}

function ToInt(t:T) : int
 ensures ToInt(t) == int(t.n);
 {
    int(t.n)
 }

method Test(x:int)
 {
    assume exists p:int :: exists t:T :: ToInt(t) > 0;
    assert exists p:int :: exists t:T :: ToInt(t) > 0;
 } 




