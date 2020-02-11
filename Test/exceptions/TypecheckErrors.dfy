// RUN: %dafny "%s" /dprint:"%t.dprint" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method TestTypecheckingInDesugaredTerm_Nat() returns (res: NatOutcome) {
    var a0 := MakeNatSuccess("not a nat");
    var a  :- MakeNatSuccess("not a nat either");
    return a0;
}

method RedeclareVar_Nat() returns (res: NatOutcome) {
    var a := MakeNatSuccess(42);
    var a :- MakeNatSuccess(43);
    var b :- MakeNatSuccess(44);
    var b := MakeNatSuccess(45);
    return a;
}

trait BadOutcome1 {
    // predicate method IsFailure() // <-- deliberately commented out
    // function method PropagateFailure(): BadOutcome1 requires IsFailure() // <-- deliberately commented out
    // function method Extract(): nat requires !IsFailure() // <-- deliberately commented out
}

trait BadOutcome2 {
    predicate method IsFailure()
    // function method PropagateFailure(): BadOutcome2 requires IsFailure() // <-- deliberately commented out
    function method Extract(): nat requires !IsFailure()
}

trait BadOutcome3 {
    predicate method IsFailure()
    function method PropagateFailure(): BadOutcome3 requires IsFailure()
    // function method Extract(): nat requires !IsFailure() // <-- deliberately commented out
}

method TestMissingMethods1(o: BadOutcome1) returns (res: BadOutcome1) {
    var a :- o; return o; // TODO infers 'BadOutcome1?' for RHS of ':-' instead of 'BadOutcome1' (should not infer nullable)
}

method TestMissingMethods2(o: BadOutcome2) returns (res: BadOutcome2) {
    var a :- o; return o; // TODO infers 'BadOutcome2?' for RHS of ':-' instead of 'BadOutcome2' (should not infer nullable)
}

method TestMissingMethods3(o: BadOutcome3) returns (res: BadOutcome3) {
    var a :- o; return o; // TODO infers 'BadOutcome3?' for RHS of ':-' instead of 'BadOutcome3' (should not infer nullable)
}

method TestTypecheckingInDesugaredTerm_Void() returns (res: VoidOutcome) {
    :- MakeVoidFailure(|"not a string because we take its length"|);
}

trait BadVoidOutcome1 {
    // predicate method IsFailure() // <-- deliberately commented out
    // function method PropagateFailure(): BadVoidOutcome1 requires IsFailure() // <-- deliberately commented out
}

trait BadVoidOutcome2 {
    predicate method IsFailure()
    // function method PropagateFailure(): BadVoidOutcome2 requires IsFailure() // <-- deliberately commented out
}

trait BadVoidOutcome3 {
    predicate method IsFailure()
    function method PropagateFailure(): BadVoidOutcome3 requires IsFailure()
    function method Extract(): nat requires !IsFailure() // <-- deliberately added, even though Void error handling must not have it
}

method TestMissingVoidMethods1(o: BadVoidOutcome1) returns (res: BadVoidOutcome1) {
    :- o; return o;
}

method TestMissingVoidMethods2(o: BadVoidOutcome2) returns (res: BadVoidOutcome2) {
    :- o; return o;
}

method TestMissingVoidMethods3(o: BadVoidOutcome3) returns (res: BadVoidOutcome3) {
    :- o; return o;
}

// ---- MultiFailures

datatype Option<T> = None | Some(get: T) {
  predicate method IsFailure()
  { None? }
  function method Extract(): T
    requires Some?
  { get }

  function method PropagateFailure<U>(): Option<U>
    requires None?
  { Option.None }
  function method PropagateFailureInt(): int
    requires None?
  { -3 }
  function method PropagateFailureThisIsReal(): real
    requires None?
  { 2.7 }
  function method PropagateFailureNoThisIs(): real
    requires None?
  { 2.7 }
}

method M0(optB: Option<bool>, optI: Option<int>) returns (u: Option<int>) {
  var b: bool :- optB;  // assigns bool or throws Option<int>
  var i: int :- optI;  // assigns int or throws Option<int>
}

method M1(optB: Option<bool>, optI: Option<int>) returns (u: int) {
  // the following will use PropagateFailureInt()
  var b: bool :- optB;  // assigns bool or throws int
  var i: int :- optI;  // assigns int or throws int
}

method M2(optB: Option<bool>, optI: Option<int>) returns (u: real) {
  // the following will find both PropagateFailureThisIsReal() and
  // PropagateFailureNoThisIs(), which is ambiguous
  var b: bool :- optB;  // error: ambiguous PropagateFailure... members
  var i: int :- optI;  // error: ambiguous PropagateFailure... members
}

method M3(opt: Option<int>) returns (u: int, v: int) {
  var i :- opt;  // error: throws one value, whereas method has two out-parameters
}

class MayThrow<T(0,==)> {
  var a: T
  var b: T
  predicate method IsFailure()
    reads this
  { a == b }
  method Extract() returns (t: T)
  { t := a; }

  function method PropagateFailure(): MayThrow<T>
  { this }
  function method PropagateFailureTakeThis(): MayThrow<T>
  { this }
  function method PropagateFailureReal(): real
  { 4.0 }
}

method N0(optB: MayThrow<bool>, optR: MayThrow<real>) returns (u: MayThrow<real>) {
  var b: bool :- optB;  // error (2x): because may throw MayThrow<bool>
}

method N1(optB: MayThrow<bool>, optR: MayThrow<real>) returns (u: MayThrow<real>) {
  // the following will find both PropagateFailure() and
  // PropagateFailureTakeThis(), which is ambiguous
  var r: real :- optR;  // error: ambiguous
}

datatype Fika = Kaffe | Te
{
  predicate method IsFailure()
  { this != Kaffe }
  function method Extract(): int
  { 100 }

  function method PropagateFailure(): real
  { 2.0 }
  function method PropagateFailureX(): Fika
  { this }
  function method PropagateFailureY(): Fika
  { this }
  function method PropagateFailureZ0(): Option<bool>
  { Option.None }
  function method PropagateFailureZ1(): Option<int>
  { Option.None }
  function method PropagateFailureW(): bool
  { true }
  function method SimonSaysW(): bool
  { true }
}

method P0(f: Fika) returns (r: real) {
  var i: int :- f;  // assigns int or throws real
}

method P1(f: Fika) returns (r: Fika) {
  var i: int :- f;  // error: ambiguous: PropagateFailureX or PropagateFailureY
}

method P2(f: Fika) returns (r: Option<real>) {
  var i: int :- f;  // error: ambiguous PropagateFailure[Z0;Z1]; error: Option<bool> not assignable to Option<real>
}

method P3(f: Fika) returns (r: bool) {
  var i: int :- f;  // fine (no ambiguity, since SimonSaysW is not considered)
  :- f;  // error: empty LHS requires no Extract method
}

datatype NoGood = NoGoodA | NoGoodB
{
  predicate method IsFailure()
  function method Extract(): int
  // note: missing plain PropagateFailure()
  function method PropagateFailureX(): real
  function method PropagateFailureY(): real
}

method Q(g: NoGood) returns (r: real)
{
  var i: int :- g;  // error: NoGood does not have IsFailure/PropagateFailure/Extract
}

// ------------------------- sans Extract

datatype SansExtract = SeYes | SeNo
{
  predicate method IsFailure() { SeNo? }
  function method PropagateFailure(): int { 7 }
  function method PropagateFailureX(): bool { false }
  function method PropagateFailureY(): bool { true }
}

method R0(s: SansExtract) returns (u: int) {
  :- s;
  var o :- s;  // error: LHS allows only when SansExtract has an Extract() member
}

method R1(s: SansExtract) returns (u: real) {
  :- s;  // error: may throw int
}

method R2(s: SansExtract) returns (u: bool) {
  :- s;  // error: ambiguous PropagateFailure[X;Y]
}
