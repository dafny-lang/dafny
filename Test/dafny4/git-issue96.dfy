// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(s:seq<int>)
    requires 10 < |s|
{
    (forall i:int {:trigger s[i]} :: forall j:int {:trigger s[j]} ::
        0 <= i < j < 5 ==> s[i + j] == s[i] == s[j])
}

predicate P0(s:seq<int>)
    requires 10 < |s|
{
    (forall i:int :: forall j:int  ::
        0 <= i < j < 5 ==> s[i + j] == s[i] == s[j])
}


predicate P1(s:seq<int>)
    requires 10 < |s|
{
    (forall i:int, j: int {:trigger s[i], s[j]} ::
        0 <= i < j < 5 ==> s[i + j] == s[i]+s[j])
}

predicate P2(s:seq<int>)
    requires 10 < |s|
{
    (forall i:int, j: int ::
        0 <= i < j < 5 ==> s[i + j] == s[i]+s[j])
}
