// RUN: %dafny /compile:0 /autoTriggers:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Transform(x:int) : int

lemma TransformProperties()
    ensures forall x1, x2 {:trigger Transform(x1), Transform(x2)} :: Transform(x1) == Transform(x2) ==> x1 == x2;       

function {:opaque} Looper(input:seq<int>) : seq<int>
    ensures |Looper(input)| == |input|;
    ensures forall i :: 0 <= i < |input| ==> Looper(input)[i] == Transform(input[i])
{
    if |input| == 0 then []
    else [Transform(input[0])] + Looper(input[1..])
}

lemma proof(s1:seq<int>, s2:seq<int>)
    requires Looper(s1) == Looper(s2);
    ensures forall i :: i in s1 <==> i in s2;
{
    reveal_Looper();
    TransformProperties();
    if |s1| != |s2| {
    } else {
        forall i | i in s1 
            ensures i in s2;
        {
            if i == s1[0] {
                assert i == s2[0];
            } else {
                assert i in s1[1..];
                proof(s1[1..], s2[1..]);
            }
        }
        forall i | i in s2 
            ensures i in s1;
        {
            if i == s2[0] {
                assert i == s1[0];
            } else {
                assert i in s2[1..];
                proof(s1[1..], s2[1..]);
            }
        }
    }
}

