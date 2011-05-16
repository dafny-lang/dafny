// This file contains various tests of resolving quantifiers in ghost and non-ghost positions

class MyClass<T> {
  // This function is in a ghost context, so all is cool.
  function GhostF(): bool
  {
    (forall n :: 2 <= n ==> (exists d :: n < d && d < 2*n))
  }
  // But try to make it a non-ghost function, and Dafny will object because it cannot compile the
  // body into code that will terminate.
  function method NonGhostF(): bool
  {
    (forall n :: 2 <= n ==> (exists d :: n < d && d < 2*n))  // error: can't figure out how to compile
  }
  // Add an upper bound to n and things are cool again.
  function method NonGhostF_Bounded(): bool
  {
    (forall n :: 2 <= n && n < 1000 ==> (exists d :: n < d && d < 2*n))
  }
  // Although the heuristics applied are syntactic, they do see through the structure of the boolean
  // operators ==>, &&, ||, and !.  Hence, the following three variations of the previous function can
  // also be compiled.
  function method NonGhostF_Or(): bool
  {
    (forall n :: !(2 <= n && n < 1000) || (exists d :: n < d && d < 2*n))
  }
  function method NonGhostF_ImpliesImplies(): bool
  {
    (forall n :: 2 <= n ==> n < 1000 ==> (exists d :: n < d && d < 2*n))
  }
  function method NonGhostF_Shunting(): bool
  {
    (forall n :: 2 <= n ==> 1000 <= n || (exists d :: n < d && d < 2*n))
  }

  function method GoodRange(): bool
  {
    (forall n | 2 <= n :: 1000 <= n || (exists d | n < d :: d < 2*n)) && (exists K: nat | K < 100 :: true)
  }
  function method BadRangeForall(): bool
  {
    forall n | n <= 2 :: 1000 <= n || n % 2 == 0  // error: cannot bound range for n
  }
  function method BadRangeExists(): bool
  {
    exists d | d < 1000 :: d < 2000  // error: cannot bound range for d
  }
  function method WhatAboutThis(): bool
  {
    forall n :: 2 <= n && (forall M | M == 1000 :: n < M) ==> n % 2 == 0  // error: heuristics don't get this one for n
  }

  // Here are more tests

  function method F(a: array<T>): bool
    requires a != null;
    reads a;
  {
    (exists i :: 0 <= i && i < a.Length / 2 && (forall j :: i <= j && j < a.Length ==> a[i] == a[j]))
  }

  function method G0(a: seq<T>): bool
  {
    (exists t :: t in a && (forall u :: u in a ==> u == t))
  }
  function method G1(a: seq<T>): bool
  {
    (exists ti :: 0 <= ti && ti < |a| && (forall ui :: 0 <= ui && ui < |a| ==> a[ui] == a[ti]))
  }

  // Regrettably, the heuristics don't know about transitivity:
  function method IsSorted0(s: seq<int>): bool
  {
    (forall i, j :: 0 <= i && i < j && j < |s| ==> s[i] <= s[j])  // error: can't figure out how to compile
  }
  function method IsSorted1(s: seq<int>): bool
  {
    (forall j, i :: 0 <= i && i < j && j < |s| ==> s[i] <= s[j])  // error: can't figure out how to compile
  }
  // Add the redundant conjunct "i < |s|" and things are fine.
  function method IsSorted2(s: seq<int>): bool
  {
    (forall i, j :: 0 <= i && i < |s| && i < j && j < |s| ==> s[i] <= s[j])
  }
  // But if you switch the order of i and j, you need a different redundant conjunct.
  function method IsSorted3(s: seq<int>): bool
  {
    (forall j, i :: 0 <= i && i < |s| && i < j && j < |s| ==> s[i] <= s[j])  // error: can't figure out how to compile
  }
  function method IsSorted4(s: seq<int>): bool
  {
    (forall j, i  :: 0 <= i && 0 < j && i < j && j < |s| ==> s[i] <= s[j])
  }

  // The heuristics look at bound variables in the order given, as is illustrated by the following
  // two functions.
  function method Order0(S: seq<set<int>>): bool
  {
    (forall i, j :: 0 <= i && i < |S| && j in S[i] ==> 0 <= j)
  }
  function method Order1(S: seq<set<int>>): bool
  {
    (forall j, i :: 0 <= i && i < |S| && j in S[i] ==> 0 <= j)  // error: can't figure out how to compile
  }

  // Quantifiers can be used in other contexts, too.
  // For example, in assert statements and assignment statements.
  method M(s: seq<int>) returns (r: bool, q: bool) {
    assert (forall x :: x in s ==> 0 <= x);
    r := (forall x :: x in s ==> x < 100);
    q := (exists y :: y*y in s);  // error: can't figure out how to compile
  }
  // And if expressions.
  function method Select_Good(S: set<int>, a: T, b: T): T
  {
    if (forall x :: x in S ==> 0 <= x && x < 100) then a else b
  }
  function method Select_Bad(S: set<int>, a: T, b: T): T
  {
    if (forall x :: x*x in S ==> 0 <= x && x < 100) then a else b  // error: can't figure out how to compile
  }
  // (the same thing, but in a ghost function is fine, though)
  function Select_Bad_Ghost(S: set<int>, a: T, b: T): T
  {
    if (forall x :: x*x in S ==> 0 <= x && x < 100) then a else b
  }
  // And if statements
  method N(s: seq<int>) returns (ghost g: int, h: int)
  {
    if ( (forall x :: x in s ==> 0 <= x) ) {
      h := 0;  g := 0;
    }
    if ( (forall x :: x*x in s ==> x < 100) ) {  // this is fine, since the whole statement is a ghost statement
      g := 2;
    }
    if ( (forall x :: x*x in s ==> x < 50) ) {
      h := 6;  // error: cannot compile this guard of a non-ghost if statement
    }
  }
}
