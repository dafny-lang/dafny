// RUN: %audit --reads-clauses-on-methods --allow-external-contracts --report-file "%t.md" "%s"
// RUN: %audit --reads-clauses-on-methods --allow-external-contracts --report-file "%t.md" --compare-report "%s"
// RUN: %audit --reads-clauses-on-methods --allow-external-contracts --report-file "%t.html" "%s"
// RUN: %audit --reads-clauses-on-methods --allow-external-contracts --report-file "%t-ietf.md" --report-format markdown-ietf "%s"
// RUN: %audit --reads-clauses-on-methods --allow-external-contracts --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.md.expect" "%t.md"
// RUN: %diff "%s.html.expect" "%t.html"
// RUN: %diff "%s-ietf.md.expect" "%t-ietf.md"
// RUN: %diff "%s.expect" "%t"

include "IgnoredAssumptions.dfy"

// Method or lemma with a failed proof (top priority, but shown only in reports from later versions of the tool)
method BadMethod(i: nat) returns (res: nat)
  requires i < 64
  ensures res == 64 - i
{
  return 64 + i;
}

// Lemma with no body
lemma MinusBv8NoBody(i: nat, j: nat)
  requires j <= i < 256
  ensures (i - j) as bv8 == i as bv8 - j as bv8

// Lemma with an {:axiom} attribute
lemma {:axiom} LeftShiftBV128(v: bv128, idx: nat)
  requires idx <= 128
  ensures v << idx == v << idx as bv8

// Function or method with an {:axiom} attribute or {:verify false} attribute

// Lemma with an assume statement in its body
lemma MinusBv8Assume(i: nat, j: nat)
  requires j <= i < 256
  ensures (i - j) as bv8 == i as bv8 - j as bv8
{
  assume (i - j) as bv8 == i as bv8 - j as bv8;
}

// Method declared {:extern} with an ensures clause and no body
newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x | 0 <= x < 0x100

method {:extern} GenerateBytes(i: int32) returns (res: seq<uint8>)
    requires i >= 0
    ensures |res| == i as int

// Method declared {:extern} with an ensures clause and a body
method {:extern} GenerateBytesWithModel(i: int32) returns (res: seq<uint8>)
    requires i >= 0
    ensures |res| == i as int
{
  return seq(i, _ => 0 as uint8);
}

// Compiled method with an assume statement with an {:axiom} attribute in its body
method GenerateBytesWrapper(i: int32) returns (res: seq<uint8>)
{
  assume {:axiom} i >= 0;
  res := GenerateBytes(i);
}

// Function or method with no body
ghost function WhoKnows(x: int): int

// Method declared {:extern} with no body and no ensures clauses
method {:extern} GenerateBytesNoGuarantee(i: int32) returns (res: seq<uint8>)
    requires i >= 0

// Extern function with postcondition. Should result in two findings.
function {:extern} ExternFunction(i: int32): (res: int32)
  ensures res != i

// Successful proof of a function, method, or lemma (shown only in reports from later versions of the tool)
method GoodMethod(i: nat) returns (res: nat)
  requires i < 64
  ensures res == 64 + i
{
  return 64 + i;
}

method DoesNotTerminate()
  decreases *
{
  DoesNotTerminate();
}

trait {:termination false} T {
}

lemma ForallWithoutBody()
  ensures forall y : int :: y != y
{
    forall y : int
      ensures y != y
}

method LoopWithoutBody(n: int)
{
    var i := 0;
    while i < n
      decreases n - i
    assert true;
}

abstract module M {
  method AbstractMethod(x: int) returns (y: int)
    ensures y > x
}

opaque function f(): int {
  0
}

// A method that's safe for concurrent use because it doesn't touch the
// heap.
method {:concurrent} ConcurrentMethod(x: int) returns (r: int) 
  reads {}
{
  return x;
}

class Box {
  ghost var value: int
}

ghost method {:concurrent} AssumedConcurrentMethod(xBox: Box)
  reads {:assume_concurrent} xBox
  modifies {:assume_concurrent} xBox
{
  xBox.value := xBox.value + 1;
}

method {:axiom} AxiomWithStuffInIt(x: int) returns (r: int) {
  assume x > 0;
  assume {:axiom} x > 10;

  forall y : int
    ensures y != y

  var i := 0;
  while i < x
    decreases x - i

  return x;
}

method AssertOnly() {
  assert {:only} true;
  assert false;
}

method {:only} MethodOnly() {
  assert false;
}

// Externs with {:axiom} (only changes whether the externs are allowed by the library backend)

method {:extern} {:axiom} GenerateBytesWithAxiom(i: int32) returns (res: seq<uint8>)
    requires i >= 0
    ensures |res| == i as int

function {:extern} {:axiom} ExternFunctionWithAxiom(i: int32): (res: int32)
  ensures res != i

module A {
  trait T {}
}
module B {
  import opened A

  @AssumeCrossModuleTermination
  class ClassExtendingTraitFromOtherModule extends T {}

  @AssumeCrossModuleTermination
  trait TraitExtendingTraitFromOtherModule extends T {}
}
