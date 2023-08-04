// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass<T> {
  var f: T
  constructor(t: T) {
    f := t;
  }
}

method M<T(0)>()
{
  var a, b := new T[100], new T[100];
  forall i | 0 <= i < 100 {
    a[3] := *;  // RHS is * -- this is okay
  }
  forall i | 0 <= i < 100 {
    a[0] := b[0];  // RHSs are the same -- this is okay
  }
  forall i | 0 <= i < 100 {
    a[0] := b[i];  // error: LHS's may be the same (while RHSs are different)
  }
}

method N<T>(a: MyClass<T>, b: MyClass<T>)
  modifies a, b
{
  var q := [a, b];
  forall i | 0 <= i < 2 {
    q[0].f := *;  // RHS is * -- this is okay
  }
  forall i | 0 <= i < 2 {
    q[0].f := q[0].f;  // RHSs are the same -- this is okay
  }
  forall i | 0 <= i < 2 {
    q[0].f := q[i].f;  // error: LHS's may be the same (while RHSs are different)
  }
}

method P<T>(t0: T, t1: T, t2: T) {
  var a: T, b: T;
  a, a, a := *, t0, *;  // only one non-* RHS per variable -- this is okay
  a, a, b, a, b := *, t1, t2, *, *;  // only one non-* RHS per variable -- this is okay
  a, a, b, a, b := *, t1, t2, t0, *;  // error: duplicate LHS -- t0 and t1 may be different
}

method Q<T>(c0: MyClass<T>, c1: MyClass<T>)
  modifies c0, c1
{
  c0.f, c1.f := c0.f, c0.f;  // okay -- RHSs are the same
  c0.f, c0.f, c0.f, c0.f := *, *, c1.f, *;  // okay -- only one RHS is non-*
  c0.f, c0.f, c0.f, c0.f := c0.f, *, c1.f, *;  // error -- duplicate LHR
}

method R<T(0)>(i: nat, j: nat)
  requires i < 10 && j < 10
{
  var a := new T[10];
  a[i], a[j] := a[5], a[5];  // okay -- RHSs are the same
  a[i], a[i], a[i], a[i] := *, *, a[5], *;  // okay -- only one RHS is non-*
  a[i], a[i], a[i], a[j] := *, a[i], a[j], a[i];  // error -- possible duplicate LHS
}

method S<T(0)>(i: nat, j: nat)
  requires i < 10 && j < 20
{
  var a := new T[10,20];
  a[i,j], a[i,i] := a[5,7], a[5,7];  // okay -- RHSs are the same
  a[i,j], a[i,j], a[i,j], a[i,j] := *, *, a[5,7], *;  // okay -- only one RHS is non-*
  a[i,j], a[i,j], a[i,j], a[i,i] := *, a[i,i], a[i,j], a[i,i];  // error -- possible duplicate LHS
}
