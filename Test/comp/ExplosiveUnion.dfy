// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ExplosiveUnion<T>(a: multiset<T>, N: nat) returns (b: multiset<T>)
  // ensures b == a^N
{
  if N == 0 {
    return multiset{};
  }
  var n := 1;
  b := a;
  while n < N
    // invariant b == a^n
  {
    b := b + b;  // double the multiplicities of every element in b
    n := n + 1;
  }
}

method Test<T>(a: multiset<T>, N: nat, t: T) {
  var b := ExplosiveUnion(a, N);
  print "There are ", b[t], " occurrences of ", t, " in the multiset\n";
}

class MyClass { }

method Main() {
  Test(multiset{}, 100, 58);  // this one should already have been working
  Test(multiset{58}, 30, 58);  // this also worked before
  Test(multiset{58}, 100, 58);  // this requires BigInteger multiplicities in multisets
  var m: multiset<MyClass?> := multiset{null};
  Test(m, 100, null);  // also test null, since the C# implementation does something different for null
}