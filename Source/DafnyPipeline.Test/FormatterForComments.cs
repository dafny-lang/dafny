using Xunit;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForComments")]
public class FormatterForComments : FormatterBaseTest {
  [Fact]
  public void FormatterWorksForCommentsHoldingTogether() {
    FormatterWorksFor(@"
   const x := 2;     /* start of comment
  These words aligned:  start */

const y := 3;", @"
const x := 2;      /* start of comment
These words aligned:  start */

const y := 3;");

    FormatterWorksFor(@"
const x := 4;
    /* start of comment
  end of comment
 should stay aligned*/
const y := 5;", @"
const x := 4;
   /* start of comment
 end of comment
should stay aligned*/
const y := 5;");

    FormatterWorksFor(@"
const x := 6;

    /* start of comment
  end of comment
 should stay aligned*/
const y := 7;", @"
const x := 6;

   /* start of comment
 end of comment
should stay aligned*/
const y := 7;");
  }


  [Fact]
  public void FormatterWorksForMultilineCommentsStartingWithRowOfStars() {
    FormatterWorksFor(@"
/***********
 * These are test cases for monotonicity of the the _k parameter.  However, monotonicity
 * does not appear to be useful in the test suite, and it is possible that the axioms
 * about monotonicity are expensive performance-wise.  Therefore, the monotonicity axioms
 * are currently not produced--they are controled by #if WILLING_TO_TAKE_THE_PERFORMANCE_HIT.
 ***********/
function test(): int
");
  }

  [Fact]
  public void FormatterWorksForConsecutiveComments() {
    var testCase = @"
abstract module M0 {
  /******* State *******/
  type State(!new)
  function DomSt(st: State): set<Path>
  function GetSt(p: Path, st: State): Artifact
    requires p in DomSt(st);

  // cached part of state
  type HashValue
  function DomC(st: State): set<HashValue>
  function Hash(p: Path): HashValue
  /* Note, in this version of the formalization and proof, we only record which things are in the
     cache.  The actual cache values can be retrieved from the system state.
  type Cmd
  function GetC(h: HashValue, st: State): Cmd
  */
  function UpdateC(cmd: string, deps: set<Path>, exps: set<string>, st: State): State

  /******* Semantics *******/

  /******* Function 'build' *******/
  function build(prog: Program, st: State, useCache: bool): Tuple<Expression, State>
    requires Legal(prog.stmts);
  {
    do(prog.stmts, st, EmptyEnv(), useCache)
  }
}
";
    FormatterWorksFor(testCase, testCase);
  }

  [Fact]
  public void FormatterWorksForCommentsOfCases() {
    FormatterWorksFor(@"
datatype Dt =
  | Int(int)
  // | ISet(iset<Dt>) //  This definition is not allowed because Dt appears in a non-strict/lax position
  // | IMap0(imap<Dt,int>) //  This definition is not allowed because Dt appears in a non-strict/lax position
  | IMap1(imap<int,Dt>)
  // | Last case commented out

method M4() {
  if {
    case true => even := noll as EvenInt;
    //case true => even := b67 as EvenInt;  // error: bv67 may be odd  // disabled because it doesn't terminate with 4.4.2 Z3
    case b67 as int % 2 == 0 => even := b67 as EvenInt;
    // case false => // Let's forget about this case
  }
}");
  }
  [Fact]
  public void FormatterWorksForAdvancedClosures() {
    FormatterWorksFor(@"
method LRead() {
  var o : object?;
  var f : Ref<() ~> bool>;
  f := new Ref<() ~> bool>;
  f.val := () reads f
              reads f.val.reads()
              reads if o in f.val.reads() then {} else {o}
    => true;
  f.val := ()
    reads f
    reads f.val.reads()
    reads if o in f.val.reads() then {} else {o}
    => true;
}

function Compose<A,B,C>(f: B ~> C, g:A ~> B): A ~> C
{
  x reads g.reads(x)
    reads if g.requires(x) then f.reads(g(x)) else {}
    requires g.requires(x)
    requires g.requires(x)
    requires f.requires(g(x))
  => f(g(x))
}

function Twice<A>(f : A ~> A): A ~> A
{
  x requires f.requires(x) && f.requires(f(x))
    reads f.reads(x), if f.requires(x) then f.reads(f(x)) else {}
  => f(f(x))
}

function Apply'<A,B>(f: A ~> B) : A ~> B
{
  x reads f.reads(x)
    requires f.requires(x)
  => f(x)
}

function TreeMapZ<A,B>(t0: Tree<A>, f: A ~> B): Tree<B>
  requires PreZ(f, TreeData(t0))
  reads PreZ.reads(f, TreeData(t0))
  decreases t0
{
  var Branch(x, ts) := t0;
  var g := t requires t in ListData(ts) && PreZ(f, TreeData(t))
             reads set x, y | x in TreeData(t) && y in f.reads(x) :: y
           => TreeMapZ(t, f);
  Branch(f(x), MapZ(ts, g))
}
");
  }

  [Fact]
  public void FormatterWorksForCommentAfterSubsetType() {
    FormatterWorksFor(@"
module R1 refines Q {
  type G = real  // specify G
  // now, it is known how to initialize
}");
  }

  [Fact]
  public void FormatterWorksForLongCommentsDocument() {
    var testCase = @"
module R {
  /* Simple comment
   * in a module
   */
  import opened LibA
}
/*
module S0 refines R {
  var x := 2
    * 3;
  // This module defines a local g().  It takes precedence over the g() that
  // comes from the (inherited) opened import
  // this is no longer possible due to too many potential clashes and generally
  // weird behaviour

  function g(): int { 2 }
*/
module V {
  /** doclike comment
    * in a module
    */
  import opened LibA
  function g(): int { 4 }
}
";
    FormatterWorksFor(testCase, testCase);
  }
  [Fact]
  public void FormatterWorksForTutorialStyle() {
    FormatterWorksFor(@"
/// Tutorial style

abstract module C {

/// Now we want this

  const x := 1

/// And then that
 
  const y := 2
}
");
  }
  [Fact]
  public void FormatterWorksForAlignedSingleLineTrailingComments() {
    var before = @"
module RefinedF refines BaseF {
  function f(): bool { false } // OK. Local f preferred over imported f
                               // even if imported into refinement parent
  lemma A() {
  forall u: int {  // regression: the inferred ensures clause used to have
                   // a problem with static const fields
    B(u);
  }
  }

  method DeclWithHavoc()
  {
    var b: int := *;  // error: technically fine, since b is never used, but here the compiler
// This comment should be on its own line
  }
}";
    var after = @"
module RefinedF refines BaseF {
  function f(): bool { false } // OK. Local f preferred over imported f
                               // even if imported into refinement parent
  lemma A() {
    forall u: int {  // regression: the inferred ensures clause used to have
                     // a problem with static const fields
      B(u);
    }
  }

  method DeclWithHavoc()
  {
    var b: int := *;  // error: technically fine, since b is never used, but here the compiler
    // This comment should be on its own line
  }
}";
    FormatterWorksFor(before, after);
  }

  [Fact]
  public void FormatterWorksForUtf8InComment() {
    FormatterWorksFor(@"
//  x ∈ a[..3] Dafny won’t prove, Wüstholz would, Mikaël doesn’t voilà Great job 
const x: int
");
  }

}