// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This identity function is used to so that if the occurrence of i below
// that is enclosed by Id gets chosen by the SMT solver as a trigger, then
// Id will be part of that trigger.  This means that the quantifier will
// not match, and thus the 'forall' statement will be useless and the method
// will not verify.  If, however, the inverting functionality in Dafny
// works properly, then the 'i' in the right-hand side of the forall assignments
// below will not be chosen in any trigger, and then the methods should
// verify.
function method Id(x: int): int { x }

method Copy<T>(a: array<T>) returns (r: array<T>)
  requires a != null;
  ensures fresh(r) && r.Length == a.Length && forall k :: 0 <= k < a.Length ==> r[k] == a[k];
{
  r := new T[a.Length];
  forall i | 0 <= i < a.Length {
    r[i] := a[Id(i)];
  }
}

method ShiftLeftA<T>(a: array<T>, n: nat) returns (r: array<T>)
  requires a != null && n <= a.Length;
  ensures fresh(r) && r.Length == a.Length - n && forall k :: n <= k < a.Length ==> r[k - n] == a[k];
{
  r := new T[a.Length - n];
  forall i | 0 <= i < a.Length - n {
    r[i] := a[i + n];
  }
}

method ShiftLeftB<T>(a: array<T>, n: nat) returns (r: array<T>)
  requires a != null && n <= a.Length;
  ensures fresh(r) && r.Length == a.Length - n && forall k :: 0 <= k < a.Length - n ==> r[k] == a[k + n];
{
  r := new T[a.Length - n];
  forall i | n <= i < a.Length {
    r[i - n] := a[Id(i)];
  }
}

method ShiftLeftC<T>(a: array<T>, n: nat) returns (r: array<T>)
  requires a != null && n <= a.Length;
  ensures fresh(r) && r.Length == a.Length - n && forall k :: 0 <= k < a.Length - n ==> r[k] == a[k + n];
{
  r := new T[a.Length - n];
  forall i | n <= i < a.Length {
    r[i + 15 - n - 15] := a[Id(i)];
  }
}

method Insert<T>(a: array<T>, p: nat, n: nat) returns (r: array<T>)
  requires a != null && p <= a.Length;
  ensures fresh(r) && r.Length == a.Length + n;
  ensures forall k :: 0 <= k < p ==> r[k] == a[k];
  ensures forall k :: p <= k < a.Length ==> r[k + n] == a[k];
{
  r := new T[a.Length + n];
  forall i | 0 <= i < a.Length {
    r[if i < p then i else i + n] := a[Id(i)];
  }
}

method RotateA<T>(a: array<T>) returns (r: array<T>)
  requires a != null;
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length];
  forall i | 0 <= i < a.Length {
    r[(i + 1) % a.Length] := a[Id(i)];  // error: Dafny does not find an inverse for this one,
                                        // which causes Z3 to pick Id(i) as the trigger, which
                                        // causes the verification to fail.
  }
}

method RotateB<T>(a: array<T>) returns (r: array<T>)
  requires a != null;
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length];
  forall i | 0 <= i < a.Length {
    r[if i + 1 == a.Length then 0 else i + 1] := a[Id(i)];  // error: Dafny does not find an inverse
                                                            // for this one, so (like in RotateA),
                                                            // the verification fails.
  }
}

method RotateC<T>(a: array<T>) returns (r: array<T>)
  requires a != null;
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length];
  forall i | 0 <= i < a.Length {
    r[if i == a.Length - 1 then 0 else i + 1] := a[Id(i)];  // yes, Dafny can invert this one
  }
}

method RotateD<T>(a: array<T>) returns (r: array<T>)
  requires a != null;
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length];
  forall i | 0 <= i < a.Length {
    r[if a.Length - 1 == i then 0 else i + 1] := a[Id(i)];  // yes, Dafny can invert this one
  }
}
