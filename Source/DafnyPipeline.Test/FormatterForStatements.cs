﻿using System.Threading.Tasks;
using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForStatements")]
public class FormatterForStatements : FormatterBaseTest {
  [Fact]
  public async Task FormatterWorksForWhileTests() {
    await FormatterWorksFor(@"
method Test() {
  rs.Close();
  ghost var qc := q.contents;
  q := Sort(q);
  assert forall k :: k in q.contents ==> k in multiset(q.contents);
  var wr := new WriterStream;
  wr.Create();

  while 0 < |q.contents|
    invariant wr.Valid() && fresh(wr.footprint)
    invariant glossary.Valid()
    invariant glossary !in wr.footprint
    invariant q !in wr.footprint
    invariant forall k :: k in q.contents ==> k in glossary.keys
  {
    var term := q.Dequeue();
    var r := glossary.Find(term);
    assert r.Some?;
    var definition := r.get;

    // write term with a html anchor
    wr.PutWordInsideTag(term, term);
    var i := 0;

    var qcon := q.contents;
    while i < |definition|
      invariant wr.Valid() && fresh(wr.footprint)
      invariant glossary.Valid()
      invariant glossary !in wr.footprint
      invariant q !in wr.footprint
      invariant qcon == q.contents
      invariant forall k :: k in q.contents ==> k in glossary.keys
    {
      var w := definition[i];
      var r := glossary.Find(w);
      if r == None {
        wr.PutWordInsideHyperlink(w, w);
      } else {
        wr.PutWord(w);
      }
      i:= i +1;
    }
  }
}");
  }

  [Fact]
  public async Task FormatterWorksForAlternatives() {
    await FormatterWorksFor(@"
method AlternativeStmt() {
  if
  {
    case x % 2 == 1 =>
      print ""odd"";
    case x % 2 == 0 =>
      print ""even"";
    // That's the last case
  }
  if
  case x % 2 == 1 =>
    print ""odd1"";
  case x % 2 == 0 =>
    print ""even1"";
  // That's the last case
}

method AlternativeLoopStmt() {
  while
    invariant x >= 0
  {
    case x % 2 == 1 =>
      print ""odd2"";
    case x % 2 == 0 =>
      print ""even2"";
    // That's the last case
  }
  while
    invariant x >= 0
  case x % 2 == 1 =>
    print ""odd3"";
  case x % 2 == 0 =>
    print ""even3"";
  // That's the last case
}
");
  }

  [Fact]
  public async Task FormatterWorksForElephantOperatorWithoutLHS() {
    await FormatterWorksFor(@"
method {:test} PassingTestUsingNoLHSAssignOrHalt() {
  :- // Comment 
    expect FailUnless(true);
  :-
    expect FailUnless(true);
}");
  }

  [Fact]
  public async Task FormatterWorksForPrintStmt() {
    await FormatterWorksFor(@"
// Sanity check
method Main() {
  print FunctionMethodSyntax.CompiledFunction()
        + GhostFunctionSyntax.CompiledFunction()
        + StillGhostFunctionSyntax.CompiledFunction()
        + BackToDefault.CompiledFunction();
  
  print
    NFunctionMethodSyntax.CompiledFunction()
    + NGhostFunctionSyntax.CompiledFunction()
    + NStillGhostFunctionSyntax.CompiledFunction()
    + NBackToDefault.CompiledFunction();
}
");
  }

  [Fact]
  public async Task FormatterWorksForIfCaseReturn() {
    await FormatterWorksFor(@"
method Test() {
  if
  case true =>
    var a := c.Plus(0);  // error: c not allocated in old state
  case true =>
    var a := c.Plus@A(0);  // error: c not allocated in state A
    return 2;
}
");
  }


  [Fact]
  public async Task FormatterWorksForElephantOperatorInMatch() {
    await FormatterWorksFor(@"
method execute_external_method(n:nat, m:nat) returns (r:Status)
{
  match n { // match statement is essential to reproduce the bug
    case 0 =>            
      :- Func1(); // elephant operator is essential to reproduce the bug
      match m {
        case 1 =>
          :- Func1();
        case _ =>
          return Success;
      }
    case _ =>
      return Success;
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForBraceAfterArrowAndSimilar() {
    await FormatterWorksFor(@"
function Test(): int {
  match s
  case None => (
    var x := 2;
    x
  )
  case Some => (
    match m
    case O => 1
  )
}
method Test() {
  match s {
    case
      1 => {
      print ""k"";
    }
    case 2
      =>
      var b := 3 by {
        LemmaCall();
      }
    case 3 => {
    }
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForLabelsBeforeIf() {
    await FormatterWorksFor(@"

method TheBreaker_AllGood(M: int, N: int, O: int)
{
  label MyLabelBlock:
  label MyLabelBlockAgain:
  if (*) {
    a := 15; break;
  }
  assert M <= i || b == 12 || e == 37;
}
");
  }

  [Fact]
  public async Task FormatterWorksForSkeletonStatement() {
    await FormatterWorksFor(@"
module ModifyStmtBreak1 refines ModifyStmtBreak0 {
  method W... {
    while true
      ...
    while ...
      invariant k == x;
    {
      k := k + 1;
    }
    modify ... {
      if * {
        break;
      } else {
        break L;
      }
    }
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForReveal() {
    await FormatterWorksFor(@"
method Foo() {
  var x := 3 by {
    reveal p.q;
  }
  x := 4 by {
    reveal p.q;
  }
  match foo {
    case Some(x) => {
      reveal x.y;
      a := b(
        c,
        d 
      );
    }
    case None => {
      a := e;
    }
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForDividedBlockStmt() {
    await FormatterWorksFor(@"
class X {
  constructor Init(x: nat)
  {
    modify `c;
    new;
    a := a + b;
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForControlFlow() {
    await FormatterWorksFor(@"
method ControlFlowTest() {
  while
    decreases O - k;
  {
    case k < O && k % 2 == 0 =>
      d := 187; break;
    case k < O =>
      if (*) { e := 4; break InnerHasLabel; }
      if (*) { e := 7; break; }
      if (*) { e := 37; break break break; }
      k := k + 1;
  }
}
");
  }
  [Fact]
  public async Task FormatterWorksForIfInLemma() {
    await FormatterWorksFor(@"
lemma AlltokenSpec(i: int)
  requires Valid()
  decreases |allTokens|
  requires 0 <= i < |allTokens|
  ensures allTokens == allTokens[..i] + allTokens[i].allTokens
{
  if i == 0 {
  } else {
    this.Next.AlltokenSpec(i - 1);
  }
}
");
  }

  [Fact]
  public async Task FormatterWorksForParticularCase() {
    await FormatterWorksFor(@"
module Test {
  lemma ProveMeThis(i: nat)
  {
    if i == 0 {
    } else if condition || TestIf(
                a,
                b,
                c
              ) {
      assert false;
    }
  }
  lemma ProveMeThis(i: nat)
  {
    if i == 0 {
    } else if
      condition ||
      TestIf(
        a,
        b,
        c
      ) {
      assert false;
    }
  }
}
");
  }
  [Fact]
  public async Task FormatterWorksForUsualMatchCasePatterns() {
    await FormatterWorksFor(@"
method test() {
  match x {
    case 1 => Bring(
      [ 1
      , 2]
    );
    case 2 => match x {
      case 1 =>
      case 2 =>
    }
  }
  var longName := match x {
    case 1 => Hello(
      arg1,
      arg2
    )
    case 2 => match z {
      case 1 => b 
      case 2 => c
    }
  };
}
", reduceBlockiness: true);
    await FormatterWorksFor(@"
method test() {
  var longName := match x {
                    case 1 => World(
                                arg3,
                                arg4
                              )
                    case 2 => match z {
                                case 1 => b 
                                case 2 => c
                              }
                  };
  match x {
    case 1 => Bring(
                [ 1
                , 2]
              );
  }
}
", reduceBlockiness: false);
  }
  [Fact]
  public async Task FormatterWorksForLabels() {
    var test = @"
method BreakLabels(s: seq<int>)
  requires |s| == 1000
{
  label A:
  for i := 0 to 100
  {
    label B:
    label C:
    for j := 100 downto 0
    {
    }
  }
}
method Test() {
  var a, b, c, d, e;
  var i := 0;
  while (i < M)
  {
    var j := 0;
    label InnerHasLabel:
    while (j < N)
    {
    }
  }
  label a:
  while {
    case true =>
      for k := 0 to 10
        invariant k <= 5
      {
        if k == 5 {
          break break;
        }
        c := c + 1;
      }
  }
  var i := 0;
  while i == 1
    decreases
      10 - i,
      1
      , 2
  {
  }
  while
    decreases
      310 - i,
      31
      , 32
  {
  }
  label Loop:
  while
    decreases 11 - i,
              12
            , 23
  {
    case i < 10 =>
      if i == 929 {
      } else if i < 7 {
        i := i + 1;
        continue Loop;
      } else {
        b := true;
        break Loop;
      }
      assert false; // unreachable
      expect false; // unreachable
  }
}
";
    await FormatterWorksFor(test, test);
  }

  public FormatterForStatements([NotNull] ITestOutputHelper output) : base(output) {
  }
}
