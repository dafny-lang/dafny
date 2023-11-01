// RUN: %testDafnyForEachResolver "%s"


type A = s : seq<int> | |s| < 10

method f(a: seq<A>)
  ensures multiset(a[..]) == multiset(a[..])
{
}
