// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This identity function is used to so that if the occurrence of i below
// that is enclosed by Id gets chosen by the SMT solver as a trigger, then
// Id will be part of that trigger.  This means that the quantifier will
// not match, and thus the 'forall' statement will be useless and the method
// will not verify.  If, however, the inverting functionality in Dafny
// works properly, then the 'i' in the right-hand side of the forall assignments
// below will not be chosen in any trigger, and then the methods should
// verify.
function Id(x: int): int { x }

method Copy<T>(a: array<T>) returns (r: array<T>)
  ensures fresh(r) && r.Length == a.Length && forall k :: 0 <= k < a.Length ==> r[k] == a[k];
{
  r := new T[a.Length](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | 0 <= i < a.Length {
    r[i] := a[Id(i)];
  }
}

method ShiftLeftA<T>(a: array<T>, n: nat) returns (r: array<T>)
  requires n <= a.Length;
  ensures fresh(r) && r.Length == a.Length - n && forall k :: n <= k < a.Length ==> r[k - n] == a[k];
{
  r := new T[a.Length - n](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | 0 <= i < a.Length - n {
    r[i] := a[i + n];
  }
}

method ShiftLeftB<T>(a: array<T>, n: nat) returns (r: array<T>)
  requires n <= a.Length;
  ensures fresh(r) && r.Length == a.Length - n && forall k :: 0 <= k < a.Length - n ==> r[k] == a[k + n];
{
  r := new T[a.Length - n](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | n <= i < a.Length {
    r[i - n] := a[Id(i)];
  }
}

method ShiftLeftC<T>(a: array<T>, n: nat) returns (r: array<T>)
  requires n <= a.Length;
  ensures fresh(r) && r.Length == a.Length - n && forall k :: 0 <= k < a.Length - n ==> r[k] == a[k + n];
{
  r := new T[a.Length - n](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | n <= i < a.Length {
    r[i + 15 - n - 15] := a[Id(i)];
  }
}

method Insert<T>(a: array<T>, p: nat, n: nat, t: T) returns (r: array<T>)
  requires p <= a.Length;
  ensures fresh(r) && r.Length == a.Length + n;
  ensures forall k :: 0 <= k < p ==> r[k] == a[k];
  ensures forall k :: p <= k < a.Length ==> r[k + n] == a[k];
{
  r := new T[a.Length + n](_ => t);
  forall i | 0 <= i < a.Length {
    r[if i < p then i else i + n] := a[Id(i)];
  }
}

method RotateA<T>(a: array<T>) returns (r: array<T>)
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | 0 <= i < a.Length {
    r[(i + 1) % a.Length] := a[Id(i)];  // error: Dafny does not find an inverse for this one,
                                        // which causes Z3 to pick Id(i) as the trigger, which
                                        // causes the verification to fail.
  }
}

method RotateB<T>(a: array<T>) returns (r: array<T>)
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | 0 <= i < a.Length {
    r[if i + 1 == a.Length then 0 else i + 1] := a[Id(i)];  // error: Dafny does not find an inverse
                                                            // for this one, so (like in RotateA),
                                                            // the verification fails.
  }
}

method RotateC<T>(a: array<T>) returns (r: array<T>)
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | 0 <= i < a.Length {
    r[if i == a.Length - 1 then 0 else i + 1] := a[Id(i)];  // yes, Dafny can invert this one
  }
}

method RotateD<T>(a: array<T>) returns (r: array<T>)
  ensures fresh(r) && r.Length == a.Length;
  ensures forall k :: 0 <= k < a.Length ==> r[(k + 1) % a.Length] == a[k];
{
  r := new T[a.Length](i requires 0 <= i < a.Length reads a => a[i]);
  forall i | 0 <= i < a.Length {
    r[if a.Length - 1 == i then 0 else i + 1] := a[Id(i)];  // yes, Dafny can invert this one
  }
}

// autoTriggers added because it causes a slight rephrasing of an error
// message.

method Zero(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 0
{
  forall i | 0 <= i < a.Length {
    a[i] := 0;
  }
}

method ZeroRange(a: array<int>)
  requires 100 <= a.Length
  modifies a
  ensures forall i :: 20 <= i < 30 ==> a[i] == 0
{
  forall i | 0 <= i < 10 {
    a[i+20] := 0;
  }
}

method ZeroRangeK(a: array<int>, k: nat)
  requires 100 <= a.Length && k <= 90
  modifies a
  ensures forall i :: k <= i < k+10 ==> a[i] == 0
{
  forall i | 0 <= i < 10 {
    a[i+k] := 0;
  }
}

method Shift(a: array<int>, b: array<int>, k: nat)
  requires b.Length == a.Length + k
  modifies b
  ensures forall i :: k <= i < b.Length ==> b[i] == a[i-k]
{
  forall i | 0 <= i < a.Length {
    b[i+k] := a[i];
  }
}

method Shift'(a: array<int>, b: array<int>, k: nat)
  requires b.Length == a.Length + k
  modifies b
  ensures forall i :: 0 <= i < a.Length ==> b[i+k] == a[i]
{
  forall i | 0 <= i < a.Length {
    b[i+k] := a[i];
  }
}

method Backwards(n: nat) returns (a: array<int>)
  ensures a.Length == n
  ensures forall i :: 0 <= i < n ==> a[i] == 0
{
  a := new int[n];
  forall i | 0 <= i < n {
    a[n-1-i] := 0;
  }
}

method DownDiagonal(n: nat) returns (a: array<int>)
  ensures a.Length == n
  ensures forall i :: 0 <= i < n ==> a[i] + i == n-1
{
  a := new int[n];
  forall i | 0 <= i < n {
    a[n-1-i] := i;
  }
}

method Nat(a: array<int>)
  requires a.Length == 20
  requires a[8] == a[13] == 200
  modifies a
  ensures a[10] == a[11] == 0
  ensures a[9] == old(a[9]) && a[12] == old(a[12])
  ensures a[8] == a[13] == 200
  // The following would be provable if the "i: nat" constraint is forgotten,
  // which would be a soundness problem.  We expect the postcondition to be
  // unprovable.
  ensures a[5] == 20  // error: possible postcondition violation
{
  forall i: nat | i < 2 {
    a[10 + i] := 0;
  }
}
