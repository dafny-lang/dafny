// RUN: %exits-with 4 %dafny /compile:0 "%s" /extractCounterexample /mv model  > "%t"
// RUN: %diff "%s.expect" "%t"

method foo(n: nat) returns (ret: array<string>)
{
    ret := new string[n];

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> j % 2 == 0 ==> ret[j] == "even"
        invariant forall j :: 0 <= j < i ==> j % 2 == 1 ==> ret[j] == "odd"
    {
        if i % 2 == 0 {
            ret[i] := "odd";
        } else {
            ret[i] := "even";
        }
        i := i + 1;
    }
}