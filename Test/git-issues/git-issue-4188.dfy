// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype T1 = nat
newtype T2 = int
newtype T3 = n: nat | true
newtype T4 = i: int | 0 <= i

method M(s1: set<T1>, s2: set<T2>, s3: set<T3>, s4: set<T4>)
  requires s1 != {} && s2 != {} && s3 != {} && s4 != {} 
{
  var i1: T1 :| i1 in s1;
  var i2: T2 :| i2 in s2;
  var i3: T3 :| i3 in s3;
  var i4: T4 :| i4 in s4;
}
