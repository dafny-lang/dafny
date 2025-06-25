// NONUNIFORM: Tests generation of shadowed variables
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method TwoVars() returns (ret: int)
  ensures ret == 1
{
  {
    var ret := true;
    return if ret then 1 else 0;
  }
}
datatype Option<T> = None | Some(i: T)
{
  predicate IsFailure() { None? }
  function PropagateFailure<U>(): Option<U> requires IsFailure() { None }
  function Extract(): T requires !IsFailure() { i }
}

method TwoVars2(i: int) returns (ret: Option<int>) {
  if i % 2 == 0 {
    var ret :- Some(Some(1));
    return Some(ret.i);
  }
  return None;
}
method Main() {
  var ret := TwoVars();
  print ret, "\n";
  var ret2 := TwoVars2(0);
  print ret2, "\n";
}