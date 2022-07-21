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

    private Newlines currentNewlines;
    [Fact]
    public void FormatterWorks() {
      ErrorReporter reporter = new ConsoleErrorReporter();
      var options = DafnyOptions.Create();
      DafnyOptions.Install(options);
      foreach (Newlines newLinesType in Enum.GetValues(typeof(Newlines))) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        var programString = @"
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
  
  least lemma l1<T>[
    nat](a: T)
  
  least lemma l2<T>[nat
    ](a: T)
  
  least lemma l3<T>
    [nat]
    (a: T)
  
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
      ensures x > 0
    {
      x := 2;
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
    && forall j: int :: j < z
                        && forall j: int :: j < z || j == y
{
  z := 0;
}";
        programString = AdjustNewlines(programString);
        var programNotIndented = indentRegex.Replace(programString, "");

        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns();
        Parser.Parse(programNotIndented, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        Assert.Equal(0, reporter.ErrorCount);
        var reprinted = TokenFormatter.__default.printSourceReindent(dafnyProgram.GetFirstTopLevelToken(),
          IndentationFormatter.ForProgram(dafnyProgram));
        Assert.Equal(programString, reprinted);

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
