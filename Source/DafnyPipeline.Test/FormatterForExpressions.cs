﻿using System.Threading.Tasks;
using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForExpressions")]
public class FormatterForExpressions : FormatterBaseTest {
  [Fact]
  public async Task FormatterWorksForFunctionsIfExprAndMatchCases() {
    await FormatterWorksFor(@"
function Zipper2<T>(a: List<T>, b: List<T>)
  : List<T>
  decreases /* max(a,b) */ if a < b then b else a,
            /* min(a,b) */ if a < b then a else b
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper2(b, c))
}
function topLevel(
  x: int,
  y: int
): int {
  if x == 2 then
    if x > 3
    then
      y
    else x
  else
    var z := 1;
    var w := z + z;
    assert w != x;
    match x {
      case 1 =>
        17 // This is the expected result

      // This case is particularly useful
      case 3 =>
        18
      case y =>
        19 
        +
        match x
        case 17 =>
          12
        case 15 =>
          16 
    }
}");
  }

  [Fact]
  public async Task FormatterWorksForCaseComments() {
    await FormatterWorksFor(@"
predicate SmallOdd(i: int) {
  match i
  // Case small odd
  case 1 => true
  case 3 => true
  // case small even
  case 0 => false
  /* Nested /*case*/ comment */
  case 2 => false
  /* All other cases */
  case i => SmallOdd(i-2)
}
method SmallOdd(i: int) returns (j: bool) {
  match i
  // Case small odd
  case 1 =>
    j := true;
  case 3 => 
    j := true;
  // case small even
  case 0 =>
    j := false;
  case 2 =>
    j := false;
  /* All other cases */
  case i =>
    j := SmallOdd(i-2);
}
");
  }

  [Fact]
  public async Task FormatterWorksForMatchStatementsAndExpressions() {
    await FormatterWorksFor(@"
method Test(z: int) {
  match
    z {
    case 0 =>
      match z + 1 {
        case 1 => print ""1"";
                  print ""1bis"";
        case 2 =>
          print ""2"";
          print ""2bis"";
        case 3
          => print ""3"";
             print ""3bis"";
      }
    case
      1 =>
    case 2
      =>
    case 3
      =>
  }
  var x :=match z
    case 1 =>
      var x := 2;
      x
    case 3 => var x := 4;
              x
    case 5
      => var x := 6;
         x
    ;
  
  var x :=(match z
           case 1 =>
             var x := 2;
             x
           case 3 => var x := 4;
                     x
           case 5
             => var x := 6;
                x
  );
  var x :=
    match z {
      case 1 => 2
      case 3 => 4
    };
}
");
  }

  [Fact]
  public async Task FormatWorksForChainedImplications() {
    await FormatterWorksFor(@"
method Test() {
  assert (1 ==>
            2 ==> 
              3);
  assert (4
          ==> 5
            ==> 6);
  assert (7
          <== 8 
          <== 9);
  assert (10 <==
          11 <== 
          12);
}");
  }

  [Fact]
  public async Task FormatWorksForFirstNestedElephantAssignments() {
    await FormatterWorksFor(@"
function TestExpressionParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome): NatOutcome {
  var expr1: nat :- (var x := if b then o1 else o2; x);
  var use_expr1: nat := expr1;
  var expr2 :- (var x := if b then o1 else o2; x);
  var use_expr2: nat := expr2;
  o2
}
");
  }

  [Fact]
  public async Task FormatterWorksForNestedIfElse() {
    var testCase = @"
function test(): int {
  if a then
    b
  else if c then
    d
  else
    e
}
";
    await FormatterWorksFor(testCase, testCase);
  }

  [Fact]
  public async Task FormatterWorksForNestedConstructors() {
    await FormatterWorksFor(@"
function test(): int {
  assert X;
  Some(Result(
         data[0],
         data[1])
  )
}
");
  }
  [Fact]
  public async Task FormatterWorksForEqualPlus() {
    await FormatterWorksFor(@"
function test(a: int, b: int, c: int): int 
  requires a == b + d + e +
                f + g + h
{ 1 }
");
  }

  [Fact]
  public async Task FormatterWorksForCommentBeforeElse() {
    await FormatterWorksFor(@"
function test(i: int): int {
  if true then
    Class.StaticMethod(argument)
  // Otherwise, we are good.
  else
    0
}
");
  }

  [Fact]
  public async Task FormatterWorksForElseWithComplexContent() {
    await FormatterWorksFor(@"
function Test(value: string): bool {
  if value == """" then Constructor(arg)
  else if value == ""1"" then Constructor1(arg)
  else match Search(value) {
         case None => Constructor(1)
         case Some(ctxVal) => None
       }
}
");
  }

  [Fact]
  public async Task FormatterWorksForAlignedOrVar() {
    await FormatterWorksFor(@"
predicate IsBinary(s: seq<int>) {
  forall i | 0 <= i < |s| ::
    || s[i] == 0
    || s[i] == 1
}");
  }

  [Fact]
  public async Task FormatterWorksForAlignedAmpVar() {
    await FormatterWorksFor(@"
method Test()
  ensures
    && P()
    && var x := 7;
    && var y := x;
    && F(x, y)
{
}
function Align(longVariableName: bool): int
{
  longVariableName &&
  var x2 := LongModuleName.LongStaticMethodName(longVariableName);
  match A
  {
    case _ => 1
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForEqualityOnItsOwnLine() {
    await FormatterWorksFor(@"
function Test(): int {
  if A then
    assert C(a1, b1, c1)
         < D(a2, b2, c2);
    assert (C(a1, b1, c1)
            < D(a2, b2, c2));
    assert (  C(a1, b1, c1)
            < D(a2, b2, c2));
    assert A
           && C(a1, b1, c1)
            < D(a2, b2, c2);
    assert A
           && C(a1, b1, c1)
              == D(a2, b2, c2);
    assert A
           &&    C(a1, b1, c1)
              == D(a2, b2, c2);
    ( C(a1, b1, c1)
      < D(a2, b2, c2) )
  else
    C(a1, b1, c1)
    == D(a2, b2, c2)
}");
  }

  [Fact]
  public async Task FormatterWorksForMatchInMap() {
    await FormatterWorksFor(@"
method AlignMapComplex(a: int) returns (r: map<string, string>) {
  return ComputeMap(map[
                      ""a"" := Compute(
                        match a {
                          case 0 => ""Zero""
                          case _ => ""NonZero""
                        })]);
}
");
  }

  [Fact]
  public async Task FormatterWorksForSeqSetMapDisplay() {
    await FormatterWorksFor(@"
function AlignSeq(): seq<seq<int>> {
  [ [ 1, 2, 3 ],
    [ 4,
      5
    , 6 ]
  , [ 7, 8, 9 ] ]
}

function AlignMap(): map<int, int> {
  map[ 1 := 2,
       2 := 3
     , 4 := 5
     , 6 :=
         7
     , 8
       := 9 ]
}

function AlignSet(): set<int> {
  { 1,
    2
  , 3} + {
    1,
    2
  , 3
  }
}
");
  }


  [Fact]
  public async Task FormatterWorksForChainingEquality() {
    await FormatterWorksFor(@"

lemma SeventeenIsNotEven()
  ensures !Even(N(17))
{
  assert Even(N(17))
      == Even(N(15)) ==
         Even(N(13)) ==
         Even(N(11))
      == 
         Even(N(9))
      == Even(N(7))
      == Even(N(5))
       < Even(N(3))
      == Even(N(1))
      == false;
}
");
  }
  [Fact]
  public async Task FormatterWorksForAligningThenAndElseIfAligned() {
    var testCase = @"
predicate Valid()
{
  data.Length == N &&
  (N == 0 ==> len == start == 0 && Contents == []) &&
  (N != 0 ==> len <= N && start < N) &&
  Contents == if start + len <= N then data[start..start+len]
                                  else data[start..] + data[..start+len-N]
}
";
    await FormatterWorksFor(testCase, testCase);
  }

  public FormatterForExpressions([NotNull] ITestOutputHelper output) : base(output) {
  }
}
