using Xunit;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForTopLevelDeclarations")]
public class FormatterForTopLevelDeclarations : FormatterBaseTest {
  [Fact]
  public void FormatterWorksForEmptyDocument() {
    FormatterWorksFor(@"
/*
module S0 refines R {
  // This module defines a local g().  It takes precedence over the g() that
  // comes from the (inherited) opened import

  // this is no longer possible due to too many potential clashes and generally
  // weird behaviour

  function g(): int { 2 }
*/
", null, true);
  }

  [Fact]
  public void FormatWorksForSingleInclude() {
    FormatterWorksFor(@"
// RUN

include ""git-issue48-include.dfyi""

");
  }
  [Fact]
  public void FormatterWorksForMultipleModules() {
    FormatterWorksFor(@"
module Outer.A {
  import B
  import C
  const a := B.b + C.c
}");
  }

  [Fact]
  public void FormatterWorksForIteratorRequiresComment() {
    FormatterWorksFor(@"
iterator Iter(x: int) yields (y: int)
  requires A: 0 <= x
  // yield requires B: 0 <= y  // not allowed; won't parse
{
}
");
  }

  [Fact]
  public void FormatWorksForTypes() {
    FormatterWorksFor(@"
type NoWitness_EffectlessArrow<!A(!new), B> = f: A ~> B  // error: cannot find witness
  | forall a :: f.reads(a) == {}
 
type X = i : int
  | i == 2 || i == 3 witness 2
 
//CommentY
type Y =   i : int
  | // Comment
    i == 2 || i == 3
    // Comment2
  witness
    // Comment3
    2
//Comment4

//CommentZ
type Z =
  i : int
  |   i == 2 ||
      i == 3
  witness 2

");
  }

  [Fact]
  public void FormatWorksForNewTypes() {
    FormatterWorksFor(@"
newtype X
  = i : int
  | || i == 2
    || i == 3 witness var x := 2;
                      x

newtype Y
  =
  i : List<int,
           int>
  | i == 2
    || i == 3
  witness
    var x := 2;
    x

");
  }

  [Fact]
  public void FormatWorksForModules() {
    FormatterWorksFor(@"
module AM { class A {}
            class B {} }

module
  AN
{  class A {}
   class B {} }

module A {
  import opened B = A
  import
    opened C = A
  import opened
    D = A
  import opened F =
    E
  import opened G
    = E
  import
    opened H =
    B
  import
    opened I
    = B
  import
    opened
    J = B
}

module M {
  export X
    extends A,
            B
    provides L1, L2
    provides L3,
             L4
    provides L5
           , L6
             // Comment
    provides
      L7, L8
    provides
      L9,
      L10
    provides
      L11
      , L12
  export Y
    extends A1
          , B1
    reveals M1, M2
    reveals M3,
            M4
    reveals M5
          , M6
            // Comment
    reveals
      M7, M8
    reveals
      M9,
      M10
    reveals
      M11
      , M12
}
trait X {
  function X(): int {
    1
  }
}
abstract module Abs {
  function X(): int
}
");
  }

  [Fact]
  public void FormatWorksForSimpleIterator() {
    FormatterWorksFor(@"
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}
");
  }
  [Fact]
  public void FormatterWorksForModules() {
    FormatterWorksFor(@"
module Tests {
class C {
  function F(c: C, d: D): bool { true }
  method M(x: int)
  { }
}
}", @"
module Tests {
  class C {
    function F(c: C, d: D): bool { true }
    method M(x: int)
    { }
  }
}");
  }

  [Fact]
  public void FormatterWorksForClassExtend() {
    FormatterWorksFor(@"
class A
  extends B<
    C<
      E
    >,
    D
  > {
}

class V
  extends 
    A,
    B
  , C {
}

class W extends 
  AA,
  BB
, CC {
}

class W
  extends  AA1,
    BB1
  , CC1 {
}

class W extends  AA2,
    BB2
  , CC2 {
}
");
  }
  [Fact]
  public void FormatterWorksForAbstractModuleDecl() {
    FormatterWorksFor(@"
abstract module C {
  export Body provides AF reveals g
 
  import AF : A`Spec
}
");
  }
  [Fact]
  public void FormatterWorksForNewtypeWithMember() {
    FormatterWorksFor(@"
newtype Even = x : int | x % 2 == 0
{
  method {:timeLimitMultiplier 4} NewtypeTest(y:int) {
    assert y == y;
  }
}

type Opaque<
    Y>
{
  static const Static: Y
  const Instance: Y
}
");
  }




}