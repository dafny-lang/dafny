// RUN: %exits-with 4 %dafny /compile:0 "%s" /extractCounterexample /mv model  > "%t"
// RUN: %diff "%s.expect" "%t"

// NB: with recent Z3 versions (e.g., 4.12.1), this program no longer
// results in the minimal counterexample that led to a crash in parsing,
// and instead results in a more useful counterexample that looks more
// like the parser would have originally expected. So this doesn't test
// what it used to test. But it's still worth testing that it doesn't
// lead to a crash or any other sort of parsing issue.
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
