// RUN: %baredafny audit --report-file "%t.md" "%s"
// RUN: %baredafny audit --report-file "%t.md" --compare-report "%s"
// RUN: %baredafny audit --report-file "%t.html" "%s"
// RUN: %baredafny audit --report-file "%t-ietf.md" --report-format markdown-ietf "%s"
// RUN: diff "%t.md" "%s.md.expect"
// RUN: diff "%t-ietf.md" "%s-ietf.md.expect"
// RUN: diff "%t.html" "%s.html.expect"

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
function WhoKnows(x: int): int

// Method declared {:extern} with no body and no ensures clauses
method {:extern} GenerateBytesNoGuarantee(i: int32) returns (res: seq<uint8>)
    requires i >= 0

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
