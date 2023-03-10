using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForComprehensions")]
public class FormatterForComprehensions : FormatterBaseTest {
  [Fact]
  public void FormatWorksForMatchExpression() {
    FormatterWorksFor(@"
predicate bad(e:Maybe)
{
  forall i :: 0 <= i < 1 ==>
                0 == match e
                     case Nothing =>
                       0
                     case Just => 0
}
predicate bad2(e:Maybe)
{
  forall i ::
    0 <= i < 1 ==>
      0 == match e case Nothing => 0
                   case Just => 0
}");
  }

  [Fact]
  public void FormatWorksForComprehensions() {
    FormatterWorksFor(@"
method comprehensions() {
  c := imap i: int |
    i % 9 == 0
    :: i % 10 == 0
    := 11;

  var a := imap
    t: int ::  t % 3
            == 4
           := 5;
  var a :=
    imap
      t: int ::  t % 3
              == 4
             := 5;

  var x := imap i: int :: i % 2 == 0 := 1;

  b := imap
    i: int
    ::
      i % 6 == 7
    :=
      8;

  b := imap
    i: int ::
    i % 6 == 7 :=
    8;

  d := imap i: int
    |  i % 12 == 0
    :: i % 13 == 0
    := 14;

  e := imap i: int |  i % 15 == 0
    ::  
      // comment
      i % 16 == 0
    :=  17;
}
");
    FormatterWorksFor(@"
method comprehensions() {
  var a := imap
             t: int ::  t % 3
                     == 4
                    := 5;

  var x := imap i: int :: i % 2 == 0 := 1;

  b := imap
         i: int
       ::
         i % 6 == 7
       :=
         8;

  c := imap i: int |
         i % 9 == 0
       :: i % 10 == 0
       := 11;

  d := imap i: int
         |  i % 12 == 0
       :: i % 13 == 0
       := 14;

  e := imap i: int |  i % 15 == 0
       ::  
         // comment
         i % 16 == 0
       :=  17;
}
", reduceBlockiness: false);
  }

  [Fact]
  public void FormatterWorksForVarsAndGhostVarsAndUnchanged() {
    FormatterWorksFor(@"
twostate predicate BadVariations(c: Twostate, d: Twostate, e: Twostate, f: Twostate)
{
  && unchanged(
       this,
       c
     )
  && old(
       c.c
     ) == c.c
  && fresh(
       c.c
     )
  && allocated(
       c.c
     )
}
lemma LeftIdentity<A,B>(x : A, f : A -> M<B>)
  ensures Bind(Return(x), f) == f(x)
{
  var State(h) := State(s => (x, s));
  var State(g2) := f(x);
  var x := new A[2](i =>
                    i + 1);
  calc {}
}

function Fu(): int
{
  ghost var p: () -> bool := P;  // error: cannot use a two-state function in this context
  ghost var q: () -> bool := YY.Sp;  // error: cannot use a two-state function in this context
  if P() then 5 else 7  // error: cannot use a two-state function here
}
");
  }

  [Fact]
  public void FormatterWorksForLinearFunctionBody() {
    FormatterWorksFor(@"
function test(): int {
  :- Need(u);
  :- Need(u);
  :- Need(u);
  var u := u as C.UnaryOpExpr;
  x
}
");
  }

  [Fact]
  public void FormatterWorksForComparisons() {
    FormatterWorksFor(@"
function f(x: int): (y: int)
  ensures x
       == y
  ensures x
        < y
  ensures x
       <= y
  ensures x
        > y
  ensures x
       >= y
  ensures x
       != y
  ensures x
     <==> y
{ 1 }
");
  }
  [Fact]
  public void FormatterWorksForForallExpressions() {
    FormatterWorksFor(@"
predicate GoodIdentifier(s: string) {
  && s != []
  && (|| 'a' <= s[0] <= 'z'
      || 'A' <= s[0] <= 'Z')
  && forall i :: 1 <= i < |s| ==>
                   || 'a' <= s[i] <= 'z'
                   || 'A' <= s[i] <= 'Z'
                   || '0' <= s[i] <= '9'
}
predicate BadIdentifier(s: string) {
  forall e, e' ::
    && Exprs.ConstructorsMatch(e, e')
    && s == """"
}
");
  }

  [Fact]
  public void FormatterWorksForSetComprehension() {
    FormatterWorksFor(@"
function test(): int {
  | set i: nat
    | i < 10
    :: i |
}
");
  }


  public FormatterForComprehensions([NotNull] ITestOutputHelper output) : base(output) {
  }
}
