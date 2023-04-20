using System.Collections.Generic;
using Bpl = Microsoft.Boogie;
using Xunit;
using Microsoft.Dafny;

namespace DafnyPipeline.Test;

[Collection("Dafny translator tests")]
public class TranslatorTest {

  private void Expect(Bpl.Expr expr, bool isAlwaysTrue, bool isAlwaysFalse) {
    Assert.Equal(isAlwaysTrue, Translator.IsExprAlways(expr, true));
    Assert.Equal(isAlwaysFalse, Translator.IsExprAlways(expr, false));
  }

  [Fact]
  public void EnsuresIsAlwaysOptimizedCorrectly() {
    var @true = new Bpl.LiteralExpr(Bpl.Token.NoToken, true);
    const bool yes = true;
    const bool no = false;
    Bpl.IToken nt = Bpl.Token.NoToken;
    Expect(@true, isAlwaysTrue: yes, isAlwaysFalse: no);

    var @false = new Bpl.LiteralExpr(nt, false);
    Expect(@false, isAlwaysTrue: no, isAlwaysFalse: yes);

    var var = new Bpl.IdentifierExpr(nt, "v");
    Expect(var, isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.Imp(@true, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(@false, var), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(var, @true), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(var, @false), isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.And(@true, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.And(@false, var), isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(Bpl.Expr.And(var, @true), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.And(var, @false), isAlwaysTrue: no, isAlwaysFalse: yes);

    Expect(Bpl.Expr.Or(@true, var), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(@false, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(var, @true), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(var, @false), isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.Not(@true), isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(Bpl.Expr.Not(@false), isAlwaysTrue: yes, isAlwaysFalse: no);

    var forallTrue = new Bpl.ForallExpr(nt, new List<Bpl.TypeVariable>(), new List<Bpl.Variable>(), @true);
    var forallFalse = new Bpl.ForallExpr(nt, new List<Bpl.TypeVariable>(), new List<Bpl.Variable>(), @false);

    Expect(forallTrue, isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(forallFalse, isAlwaysTrue: no, isAlwaysFalse: no);

    var existsTrue = new Bpl.ExistsExpr(nt, new List<Bpl.Variable>(), @true);
    var existsFalse = new Bpl.ExistsExpr(nt, new List<Bpl.Variable>(), @false);

    Expect(existsFalse, isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(existsTrue, isAlwaysTrue: no, isAlwaysFalse: no);

    var forallFalseImpliesSomething = new Bpl.ForallExpr(nt, new List<Bpl.TypeVariable>(), new List<Bpl.Variable>(), Bpl.Expr.Imp(@false, var));
    Expect(forallFalseImpliesSomething, isAlwaysTrue: yes, isAlwaysFalse: no);
  }

  // Test of embedding code into proof obligation descriptions

  [Fact]
  public void DivisionByZero() {
    ShouldHaveImplicitCode(@"
method Test(x: int, y: int) returns (z: int) {
  z := 2 / (x + y); // Here
}
", "x + y != 0");
  }

  [Fact]
  public void FunctionPrecondition() {
    ShouldHaveImplicitCode(@"
method Test(x: int, y: int) returns (z: int) {
  z := HasPrecond(x + y); // Here
}
function HasPrecond(k: int): int
  requires k % 10 != 0
{
  120 / (k % 10)
}
", "(x + y) % 10 != 0");
  }


  [Fact]
  public void ClosurePrecondition() {
    ShouldHaveImplicitCode(@"
method Test(x: int, y: int; HasPrecond: int --> int) returns (z: int) {
  z := HasPrecond(x + y); // Here
}
", "HasPrecond.requires(x + y)");
  }

  [Fact]
  public void CompilableAssignSuchThat() {
    ShouldHaveImplicitCode(@"
predicate P(x: int)
 
function Test(x: int, z: int): int
  requires P(z) && x <= z
{
  var b :| x <= b && P(b); // Here
  b
}
", "forall x0, y0 :: x <= x0 && P(x0) && x <= y0 && P(y0) ==> x0 == y0");
  }

  [Fact]
  public void AssignmentSuchThatShouldExist() {
    ShouldHaveImplicitCode(@"
predicate P(x: int)
 
lemma PUnique(a: int)
  ensures forall x, y | a <= x && a <= y :: P(x) == P(y) ==> x == y

function Test(x: int): int
{
  PUnique(x);
  var b :| x <= b && P(b); // Here
  b
}
", "exists b :: x <= b && P(b)");
  }

  [Fact]
  public void ArrayIndexOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3]; // Here
}
", "0 <= i + 3 < |a(2)|");
  }

  [Fact]
  public void ArraySliceLowerOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3..]; // Here
}
", "0 <= i + 3 <= |a(2)|");
  }

  [Fact]
  public void ArrayUpperOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int, j: int) {
  var b := a(2)[j..i + 3]; // Here
}
", "j <= i + 3 <= |a(2)|");
  }

  [Fact]
  public void SubsetTypeConstraint() {
    ShouldHaveImplicitCode(@"
function method increment(i: int): int
  requires i > 0 { i + 1 }

method Call(fn: int -> int) {
    var x := fn(-1);
}

method Main() {
  Call(increment); // here
}
", "forall i: int :: increment.requires(i)");
  }

  [Fact]
  public void DecreasesClause() {
    ShouldHaveImplicitCode(@"
function F(i: nat): nat

function Recursive(i: nat, j: nat): int
{
  if i == 0 then 0 else
    Recursive(F(i) + F(i+1), F(j)) // Here
}
", "F(i) + F(i+1) < i || (F(i) + F(i+1) == i && F(j) < j)");
  }

  [Fact]
  public void ElementNotInDomain() {
    ShouldHaveImplicitCode(@"
method Test(m: map<int, int>, x: int) {
  var b := m[x + 2]; // Here
}
", "x + 2 in m");
  }

  [Fact]
  public void WitnessCheck() {
    ShouldHaveImplicitCode(@"
function f(): int

type GreaterThanF = x: int | x >= f() witness 5 // Here

", "5 >= f()");
  }

  [Fact]
  public void NonNull() {
    ShouldHaveImplicitCode(@"
class A {
  var x: int;
}
method Test(a: int -> A?) {
  var b := a(2).x;
}
", "a(2) != null");
  }

  [Fact]
  public void Allocated() {
    ShouldHaveImplicitCode(@"
class C {
  constructor() {}
  var x: int
}
method f() {
  var c := new C();
  assert old(c.x == 1); // here
}
", "allocated(c)");
  }

  [Fact]
  public void AsInt() {
    ShouldHaveImplicitCode(@"
function g(): real

method f() {
  var n := g() as int; // Here
}
", "g().Floor as real == g()");
  }

  [Fact]
  public void FitBv() {
    ShouldHaveImplicitCode(@"
function g(): real

method f(x: bv16) {
  var y := x as bv8; // Here
}
", "x < (1 << 8)");
  }

  [Fact]
  public void IntFitsChar() {
    ShouldHaveImplicitCode(@"
method f(x: int) {
  var y := x as char; // Here
}
", "(0 <= x && x < 55296) || (57344 <= x && x < 1114112)");
    var notUnicode = new DafnyOptions {
      UnicodeOutput = false
    };
    ShouldHaveImplicitCode(@"
method f(x: int) {
  var y := x as char; // Here
}
", "0 <= x && x < 65536", notUnicode);
  }

  [Fact]
  public void SeqDecreases() {
    ShouldHaveImplicitCode(@"
method f(x: seq<int>, y: seq<int>)
  decreases x
{
  if |x| > 0 {
    assert ;
    f(y, x);
  }
}
", "|y| < |x| && y == x[0..|y|]");
  }


  [Fact]
  public void BoolDecreases() {
    ShouldHaveImplicitCode(@"
predicate P1(b: bool)
predicate P2(b: bool)
predicate P3(b: bool)

method f(x: bool, y: bool, z: bool)
  decreases x, y, z
{
  assert (!P1(x) && x) ||
    (P1(x) == x && ((!P2(y) && y) || 
    (P2(y) == y && (!P3(z) && z))));
  f(P1(x), P2(y), P3(z));
}
", "(!P1(x) && x) || (P1(x) == x && ((!P2(y) && y) || (P2(y) == y && (!P3(z) && z))))");
  }

  [Fact]
  public void DatatypeDecreases() {
    ShouldHaveImplicitCode(@"
datatype X = A(x: X) | B(x: X) | C

function D(x: X): X

function Test(x: X): int {
  if x != C then
    Test(D(x)) // Here
  else
    0
}
", "D(x) < x");
  }

  [Fact]
  public void RealFitsChar() {
    ShouldHaveImplicitCode(@"
method f(x: real)
  requires x.Floor as real == x
{
  var y := x as char; // Here
}
", "(0.0 <= x && x < 55296.0) || (57344.0 <= x && x < 1114112.0)");
    var notUnicode = new DafnyOptions {
      UnicodeOutput = false
    };
    ShouldHaveImplicitCode(@"
method f(x: real)
  requires x.Floor as real == x
{
  var y := x as char; // Here
}
", "0.0 <= x && x < 65536.0", notUnicode);
  }

  [Fact]
  public void ToOrdinalNeedsPositive() {
    ShouldHaveImplicitCode(@"
method f(x: int)
{
  var y := x as ORDINAL; // Here
}
", "0 <= x");

    ShouldHaveImplicitCode(@"
method f(x: real)
  requires x.Floor as real == x;
{
  var y := x as ORDINAL; // Here
}
", "0.0 <= x");
  }

  private void ShouldHaveImplicitCode(string program, string expected, DafnyOptions options = null) {
    Assert.True(false);
    // Parse, resolve and translate the program
    // Verify that the assertion has a proof obligation with a code that,
    // if printed, yield the given.
  }
}
