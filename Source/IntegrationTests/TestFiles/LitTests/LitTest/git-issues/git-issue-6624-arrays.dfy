// RUN: %exits-with 4 %verify --type-system-refresh:false --general-newtypes:false --general-traits:legacy "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The refreshed resolver currently fails before verification for these array targets.
datatype Res<T> = Ok(v: T) | Fail {
  predicate IsFailure() { Fail? }
  function PropagateFailure<U>(): Res<U> requires IsFailure() { Fail }
  function Extract(): T requires !IsFailure() { v }
}
method ArrayUnequal(a: array<int>) returns (out: Res<int>)
  requires a.Length > 0
  modifies a
{
  a[0], a[0] :- Ok(1), 2;
  out := Ok(0);
}
method ArrayEqual<T>(a: array<T>, value: T) returns (out: Res<T>)
  requires a.Length > 0
  modifies a
{
  a[0], a[0] :- Ok(value), value;
  out := Ok(value);
}
method InitialAlias(a: array<int>, i: int, j: int) returns (out: Res<int>)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  requires i == j
  modifies a
{
  var k := i;
  a[k], k, a[j] :- Ok(1), j + 1, 2;
  out := Ok(k);
}
method InitialDistinct(a: array<int>, i: int, j: int) returns (out: Res<int>)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  requires i != j
  modifies a
{
  var k := i;
  a[k], k, a[j] :- Ok(1), j, 2;
  assert a[i] == 1 && a[j] == 2;
  out := Ok(k);
}
method MultipleLocations(a: array<int>, i: int, j: int, k: int) returns (out: Res<int>)
  requires 0 <= i < a.Length && 0 <= j < a.Length && 0 <= k < a.Length
  requires i == j && j != k
  modifies a
{
  a[i], a[j], a[k] :- Ok(1), 2, 3;
  out := Ok(0);
}
method MultiArrayEqual(a: array2<int>) returns (out: Res<int>)
  requires a.Length0 > 0 && a.Length1 > 0
  modifies a
{
  a[0, 0], a[0, 0] :- Ok(1), 1;
  out := Ok(0);
}
method MultiArrayUnequal(a: array2<int>) returns (out: Res<int>)
  requires a.Length0 > 0 && a.Length1 > 0
  modifies a
{
  a[0, 0], a[0, 0] :- Ok(1), 2;
  out := Ok(0);
}
