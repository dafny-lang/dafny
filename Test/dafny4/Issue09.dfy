// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function Transform(x:int) : int

lemma TransformProperties()
    ensures forall x1, x2 {:trigger Transform(x1), Transform(x2)} :: Transform(x1) == Transform(x2) ==> x1 == x2;

ghost function {:opaque} Looper(input:seq<int>) : seq<int>
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
}

