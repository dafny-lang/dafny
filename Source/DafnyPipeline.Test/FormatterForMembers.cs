using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForMembers")]
public class FormatterForMembers : FormatterBaseTest {
  [Fact]
  public void FormatterWorksForMethodsInModule() {
    FormatterWorksFor(@"
import opened Test
module Test {
  method f1<T, U>(a: T, b: U)
  
  method
    f2<T, U>(a: T, b: U)
  
  method f3
    <T, U>(a: T, b: U)
  
  method f4
    <  T
       // The definition of T
    ,  U>(a: T, b: U)
  
  method f5
    <   T,
        U>(a: T, b: U)
  
  method f6
    <    T,
         U
    >(a: T, b: U)
  
  method f7
    <
      T(00),
      U>(a: T, b: U)
  
  method f8
    <
      T(00),
      U
    >(a: T, b: U)
  
  method f9<
      T, U>(a: T, b: U)
  
  method f10< T
            , U>(a: T, b: U)
  
  method g0(a: int, b: int)
  
  method g1
  (a: int, b: int)
  
  method g2
  (a: int, b: int)
  
  method g3
  (
    a: int, b: int)
  
  method g4
  (
    a: int,
    b: int)
  
  method g5
  (  a: int,
     b: int)
  
  method g6
  (   a: int
  ,   b: int)
  
  method g7(
    a: int,
    b: int)
  
  method g8(
    a: int,
    b: int
  )
  
  method g9(
    a: int
  , b: int
  )
  
  method r1() returns (a: int, b: int) {}
  
  method r2()
    returns (a: int, b: int) {}
  
  method r3() returns
    (a: int, b: int) {}
  
  method r4()
    returns
    (a: int, b: int) {}
  
  method r5()
    returns (
      a: int,
      b: int) {}
  
  method r6()
    returns 
    (   a: int,
        b: int) {}
  
  method r7()
    returns 
    (   a: int
    ,   b: int) {}
  
  method r8()
    returns 
    (   a: int
    ,   b: int
    ) {}
  
  method r9()
    returns 
    (   
      a: int,
      b: int) {}
  least lemma l1<T>[
      nat](a: T)
  
  least lemma l3<T>
    [nat]
  (a: T)
  
  least lemma l2<T>[nat
    ](a: T)
  
}");
  }

  [Fact]
  public void FormatWorksForFunctionMethods() {
    FormatterWorksFor(@"
function Test(): int {
  1
} by method {
  var i: nat := 0;
  assert IsScriptForward(edits[..0], |s|) by {
    reveal IsScriptForward();
  }
}");
  }

  [Fact]
  public void FormatWorksForFunctionByMethods() {
    FormatterWorksFor(@"
function Fib(i: nat): nat {
  1
} by method {
  if i <= 1 { return i; }
  var a, b, t := 0, 1, 1;
  for t := 1 to i
    invariant && b == Fib(t)
              && a == Fib(t-1) {
    a, b := b, a + b;
  }
  return b;
}");
  }

  [Fact]
  public void FormatWorksConstant() {
    FormatterWorksFor(@"
class T {
  const x
    : int
    := var y := 17;
       y + y
  
  // Comment
}");
  }
  [Fact]
  public void FormatterWorksForConstants() {
    FormatterWorksFor(@"
const c :=
  1111111111111111111111111111111111111111
const ASSIGNED_PLANES := [
  0,
  1,
  2
]
const ASSIGNED_PLANES: set<bv8> := {
  0,
  1,
  2
}
const ASSIGNED_PLANES := (
  0,
  1,
  2
)
");
  }

  [Fact]
  public void FormatterWorksForExtremePredicates() {
    FormatterWorksFor(@"
lemma Lemma(k: ORDINAL, r: real)
  requires E.P(r)
  requires E.P#[k](r)
{}");
  }

  [Fact]
  public void FormatterWorksForSmokeTest() {
    FormatterWorksFor(@"
include ""../libraries/src/Wrappers.dfy""
import opened Wrappers

method id<T>(r: T) returns (r2: T)  {
  r2 := r;
}

method test(s: string) returns (r: Option<string>) {
  r := None;
  var x :- id<Option<string>>(Some(s));
  r := Some(x);
}

method Main() {
  var x := test(""ok"");
  if x.Some? {
    print x.value;
  } else {
    print ""None?!"";
  }
}
", @"
include ""../libraries/src/Wrappers.dfy""
import opened Wrappers

method id<T>(r: T) returns (r2: T)  {
  r2 := r;
}

method test(s: string) returns (r: Option<string>) {
  r := None;
  var x :- id<Option<string>>(Some(s));
  r := Some(x);
}

method Main() {
  var x := test(""ok"");
  if x.Some? {
    print x.value;
  } else {
    print ""None?!"";
  }
}
");
  }


  public FormatterForMembers([NotNull] ITestOutputHelper output) : base(output)
  {
  }
}
