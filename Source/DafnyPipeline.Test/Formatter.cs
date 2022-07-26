using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Microsoft.Dafny.Helpers;
using Xunit;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Formatter")]
  public class Formatter {
    enum Newlines { LF, CR, CRLF };

    private static Regex indentRegex = new Regex(@"(?<=\n|\r(?!\n))[ \t]*");

    private static Regex removeTrailingNewlineRegex = new Regex(@"(?<=\S)[ \t]+(?=\r?\n|\r(?!\n))");

    private Newlines currentNewlines;

    [Fact]
    public void FormatterWorksForAssignments() {
      FormatterWorksFor(@"method test() {
  var
    x
    :=
    1;
  var y := 3;
  x := 2;
  x :=
    3;
  x := 4
    ;
  x
    := 4;
  x
    :=
    4;
  x, y :=
    2, 3;
}");
    }

    [Fact]
    public void FormatterWorksForModulesClassesSpecsForallWhileForLoopIfWhile() {
      FormatterWorksFor(@"
module Test {
  method f1<T, U>(a: T, b: U)
  
  method
    f2<T, U>(a: T, b: U)
  
  method f3
    <T, U>(a: T, b: U)
  
  method f4
    <  T
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
  
  /** A comment
    * Followed by newline
    * This is the end */
  module Indented {
    /* Multiline comment
     * should be indented like that
     */
    // Multiple comments
    // One per line
    method Weird()
      returns (x: int)
      // One in the docstring
      ensures &&  x > 1
              && 
                  x > 2
              &&  x > 3 &&
                  x > 4
      ensures
        && x > 5
        && x > 6
      ensures
        x > 7
        && x > 8
      ensures
        x > 9 &&
        x > 10
    {
      x := 11;
    }
    class A {
      static method f() {
        // A comment
        var x := 2;
      }
    }
  }
}

method topLevel(
    x: int,
    y: int
  ) returns (z: int)
  ensures z > 10
  ensures
    && (forall j: int :: j < z || j == x)
    && forall w: int :: w < z
                        && forall j: int :: j < z || j == y
{
  z := 0;
  if z == 0 {
    if
      z == 1
    {
      z := z / 0;
    }
    else
    {
      z := 1;
    }
  } else {
    z := 0;
  }
  forall z <- [0]
    ensures 1 == 1 {
    assert true;
  }
  forall z <- [0]
    ensures 0 == 0
  {
    assert true;
  }
  
  forall z <- [0]
    ensures
      0 == 0
  {
    assert true;
  }
  while z != 0
    invariant true {
    z := 0;
  }
  while
    z != 0
    invariant true {
    z := 0;
  }
  while
    z != 0
    invariant true
  {
    z := 0;
  }
  for i := 0 to 1 {
    assert true;
  }
  for i :=
    0 to 1 {
    assert true;
  }
  for i := 0 to 1
    invariant true
  {
    assert true;
  }
  var x :=
    2;
  var
    x :=
    2;
  var
    x
    ,
    y
    :=
    2
    ,
    3
    ;
  var z
    , 
      w
    :=
    4
    ,
    5
    ;
  var y,
      z
    := x,
       1;
  var b
    , c
    := d
     , e;
  var y
    , z :=
    x
    , 1;
  var
    y,
    z
    :=
    x
    ,1;
  var w :|
    true;
}
// Trailing comments
");
    }

    [Fact]
    public void FormatterWorksForFunctions() {
      FormatterWorksFor(@"
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
      17
    case 3 =>
      18
    case y =>
      19 
      + 1 
    }
}");
    }

    [Fact]
    public void FormatterworksForMatchStatementsAndExpressions() {
      FormatterWorksFor(@"
method Test(z: int) {
  match
    z {
  case 0 =>
    match z + 1 {
    case 1 => print ""ok"";
              print ""second"";
    case 1 =>
      print ""ok"";
      print ""second"";
    case 2
      => print ""ok"";
         print ""second"";
    }
  case
    1 =>
  case 2
    =>
  case 3
    =>
  }
  var x :=match z {
          case 1 =>
            var x := 2;
            x
          case 3 => var x := 4;
                    x
          case 5
            => var x := 6;
               x
          };
  var x :=
    match z {
    case 1 => 2
    case 3 => 4
    };
}
");
    }

    private void FormatterWorksFor(string programString) {
      ErrorReporter reporter = new ConsoleErrorReporter();
      var options = DafnyOptions.Create();
      DafnyOptions.Install(options);
      foreach (Newlines newLinesType in Enum.GetValues(typeof(Newlines))) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        programString = AdjustNewlines(programString);
        var programNotIndented = indentRegex.Replace(programString, "");
        var expectedProgram = removeTrailingNewlineRegex.Replace(programString, "");

        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns();
        Parser.Parse(programNotIndented, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        Assert.Equal(0, reporter.ErrorCount);
        var reprinted = TokenFormatter.__default.printSourceReindent(dafnyProgram.GetFirstTopLevelToken(),
          IndentationFormatter.ForProgram(dafnyProgram));
        Assert.Equal(expectedProgram, reprinted);

        // Verify that the formatting is stable.
        module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        Microsoft.Dafny.Type.ResetScopes();
        builtIns = new BuiltIns();
        Parser.Parse(reprinted, "virtual", "virtual", module, builtIns, reporter);
        dafnyProgram = new Program("programName", module, builtIns, reporter);
        Assert.Equal(0, reporter.ErrorCount);
        var reprinted2 = TokenFormatter.__default.printSourceReindent(dafnyProgram.GetFirstTopLevelToken(),
          IndentationFormatter.ForProgram(dafnyProgram));
        Assert.Equal(reprinted, reprinted2);
      }
    }

    private string AdjustNewlines(string programString) {
      return currentNewlines switch {
        Newlines.LF => new Regex("\r?\n").Replace(programString, "\n"),
        Newlines.CR => new Regex("\r?\n").Replace(programString, "\r"),
        _ => new Regex("\r?\n").Replace(programString, "\r\n")
      };
    }

    private void AssertTrivia(TopLevelDecl topLevelDecl, string triviaBefore, string triviaDoc) {
      Assert.Equal(AdjustNewlines(triviaBefore), topLevelDecl.StartToken.LeadingTrivia);
      Assert.Equal(AdjustNewlines(triviaDoc), topLevelDecl.TokenWithTrailingDocString.TrailingTrivia);
    }

    private void AssertTrivia(MemberDecl topLevelDecl, string triviaBefore, string triviaDoc) {
      Assert.Equal(AdjustNewlines(triviaBefore), topLevelDecl.StartToken.LeadingTrivia);
      Assert.Equal(AdjustNewlines(triviaDoc), topLevelDecl.TokenWithTrailingDocString.TrailingTrivia);
    }
  }
}
