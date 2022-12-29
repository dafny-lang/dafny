// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T(n:int)
function P(x: int) : int { x - 1}

function ToInt(t:T) : int
 ensures ToInt(t) == t.n as int;
 {
    t.n as int
 }

method Test(x:int)
 {
    assume exists p:int :: exists t:T :: ToInt(t) > 0;
    assert exists p:int :: exists t:T :: ToInt(t) > 0;
 }




