// RUN: %exits-with 4 %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %exits-with 4 %verify --type-system-refresh:false --general-newtypes:false --general-traits:legacy --allow-warnings "%s" > "%t"
// RUN: %diff "%s.legacy.expect" "%t"

datatype Res<T> = Ok(v: T) | Fail {
  predicate IsFailure() { Fail? }
  function PropagateFailure<U>(): Res<U> requires IsFailure() { Fail }
  function Extract(): T requires !IsFailure() { v }
}
method LocalUnequal() returns (out: Res<int>) {
  var x: int;
  x, x :- Ok(1), 2;
  out := Ok(x);
}
method LocalEqual() returns (out: Res<int>) {
  var x: int;
  x, x :- Ok(1), 1;
  assert x == 1;
  out := Ok(x);
}
method FailureAlias() returns (out: Res<int>) {
  var x: int;
  x, x :- Fail, 2;
  out := Ok(x);
}
method FailureDistinct() returns (out: Res<int>) {
  var x: int; var y: int;
  x, y :- Fail, 2;
  out := Ok(x + y);
}
method MultipleAliases() returns (out: Res<int>) {
  var x: int;
  x, x, x :- Ok(1), 1, 1;
  out := Ok(x);
}
class Box<T> {
  var value: T
  constructor(v: T) { value := v; }
}
method GenericEqual<T>(b: Box<T>, value: T) returns (out: Res<T>) modifies b {
  b.value, b.value :- Ok(value), value;
  out := Ok(b.value);
}
method GenericUnequal<T>(b: Box<T>, one: T, two: T) returns (out: Res<T>)
 requires one != two
 modifies b
{
  b.value, b.value :- Ok(one), two;
  out := Ok(b.value);
}
class HeapStatus {
  var payload: int
  var offset: int
  predicate IsFailure() { false }
  function PropagateFailure(): HeapStatus requires IsFailure() { this }
  function Extract(): int reads this { payload + offset }
}
method HeapEqual(r: HeapStatus) returns (out: HeapStatus)
  requires r.offset == 0
  modifies r
{
  r.payload, r.payload :- r, 2;
  assert r.payload == 2;
  out := r;
}
method HeapUnequal(r: HeapStatus) returns (out: HeapStatus)
  requires r.offset == 1
  modifies r
{
  r.payload, r.payload :- r, 2;
  out := r;
}
class MethodStatus {
  var payload: int
  var result: int
  predicate IsFailure() { false }
  function PropagateFailure(): MethodStatus requires IsFailure() { this }
  method Extract() returns (value: int)
    modifies this
    ensures value == old(result)
  {
    value := result;
    payload := 99;
  }
}
method MethodEqual(r: MethodStatus) returns (out: MethodStatus)
  requires r.result == 1
  modifies r
{
  r.payload, r.payload :- r, 1;
  assert r.payload == 1;
  out := r;
}
method MethodUnequal(r: MethodStatus) returns (out: MethodStatus)
  requires r.result == 2
  modifies r
{
  r.payload, r.payload :- r, 1;
  out := r;
}
method ExpectEqual() {
  var x: int;
  x, x :- expect Ok(1), 1;
  assert x == 1;
}
method AssertEqual() {
  var x: int;
  x, x :- assert Ok(1), 1;
  assert x == 1;
}
method AssumeEqual() {
  var x: int;
  x, x :- assume {:axiom} Ok(1), 1;
  assert x == 1;
}
method HavocAlias() returns (out: Res<int>) {
  var x: int;
  x, x :- Ok(1), *;
  out := Ok(x);
}
method HavocDistinct() returns (out: Res<int>) {
  var x: int; var y: int;
  x, y :- Ok(1), *;
  out := Ok(x);
}
trait Slot<T> extends object { var value: T }
class IntSlot extends Slot<int> {
  constructor() {
    value, value :- expect Ok(1), 1;
  }
}
method Pair() returns (r: Res<int>, value: int)
  ensures r == Ok(1) && value == 1
{
  r := Ok(1); value := 1;
}
method CallAlias() returns (out: Res<int>) {
  var x: int;
  x, x :- Pair();
  out := Ok(x);
}
method AssignmentEqual() {
  var x: int;
  x, x := 1, 1;
  assert x == 1;
}
method AssignmentUnequal() {
  var x: int;
  x, x := 1, 2;
}
datatype Status = Success | Failure {
  predicate IsFailure() { Failure? }
  function PropagateFailure(): Status requires IsFailure() { Failure }
}
method StatusEqual() returns (out: Status) {
  var x: int;
  x, x :- Success, 1, 1;
  assert x == 1;
  out := Success;
}
method StatusUnequal() returns (out: Status) {
  var x: int;
  x, x :- Success, 1, 2;
  out := Success;
}
method DistinctReceivers(one: Box<int>, two: Box<int>) returns (out: Res<int>)
  requires one != two
  modifies one, two
{
  var receiver := one;
  receiver.value, receiver, two.value :- Ok(1), two, 2;
  assert one.value == 1 && two.value == 2;
  out := Ok(0);
}
method AliasedReceivers(one: Box<int>, two: Box<int>) returns (out: Res<int>)
  requires one != two
  modifies one, two
{
  var receiver := one;
  receiver.value, receiver, one.value :- Ok(1), two, 2;
  out := Ok(0);
}
datatype Tag = A | B
method ClonedAlias(tag: Tag) returns (out: Res<int>) {
  match tag {
    case A | B =>
      var x: int;
      x, x :- Ok(1), 2;
      out := Ok(x);
  }
}
method ClonedEqual(tag: Tag) returns (out: Res<int>) {
  match tag {
    case A | B =>
      var x: int;
      x, x :- Ok(1), 1;
      out := Ok(x);
  }
}
method ExpectUnequal() {
  var x: int;
  x, x :- expect Ok(1), 2;
}
method AssertUnequal() {
  var x: int;
  x, x :- assert Ok(1), 2;
}
method AssumeUnequal() {
  var x: int;
  x, x :- assume {:axiom} Ok(1), 2;
}
method FailureWrites(one: Box<int>, two: Box<int>) returns (out: Res<int>)
  requires one != two
  modifies one, two
  ensures out.Fail? && two.value == 2
{
  one.value, two.value :- Fail, 2;
  out := Ok(0);
}
