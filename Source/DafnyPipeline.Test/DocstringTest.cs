#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {

  // Simple test cases (FormatterWorksFor with only one argument)
  // consist of removing all the indentation from the program,
  // adding it through the formatter, and checking if we obtain the initial result
  //
  // Advanced test cases consist of passing the program and its expected result after indentation
  //
  // Every test is performed with all three newline styles
  // Every formatted program is formatted again to verify that it stays the same.
  public class DocstringTest {
    enum Newlines {
      LF,
      CR,
      CRLF
    };

    private Newlines currentNewlines;

    [Fact]
    public void DocstringWorksForFunctions() {
      DocstringWorksFor(@"
function Test1(i: int): int
  // Test1 computes an int
  // It takes an int and adds 1 to it
{ i + 1 }

function Test2(i: int): int
  //Test2 computes an int
  //It takes an int and adds 2 to it
{ i + 2 }
// Trailing comment

// Test3 computes an int
// It takes an int and adds 3 to it
ghost function Test3(i: int): int
{ i + 3 }

// this is not a docstring but can be used as a TODO
function Test4(i: int): int
  // Test4 computes an int
  // It takes an int and adds 4 to it
{ i + 4 }

function Test5(i: int): int
  /* Test5 computes an int
   * It takes an int and adds 5 to it */
{ i + 5 }

function Test6(i: int): int
/** Test6 computes an int
  * It takes an int and adds 6 to it */

function Test7(i: int): (j: int)
  /* Test7 computes an int
  It takes an int and adds 7 to it */
{ i + 7 }

function Test8(i: int): int
  /* Test8 computes an int
     It takes an int and adds 8 to it */
{ i + 8 }

function Test9(i: int): int /*
  Test9 computes an int
  It takes an int and adds 9 to it */
{ i + 9 }

function Test10(i: int): int
  /* Test10 computes an int
      It takes an int and adds 10 to it */
{ i + 10 }

function Test11(i: int): int
  /** Test11 computes an int
    *  It takes an int and adds 11 to it */
{ i + 11 }
", Enumerable.Range(1, 9).Select(i =>
        ($"Test{i}", (string?)$"Test{i} computes an int\nIt takes an int and adds {i} to it")
        ).Concat(
        new List<(string, string?)>() {
          ($"Test10", $"Test10 computes an int\n It takes an int and adds 10 to it"),
          ($"Test11", $"Test11 computes an int\n It takes an int and adds 11 to it")
        }
        ).ToList());
    }

    [Fact]
    public void DocstringWorksForPredicate() {
      DocstringWorksFor(@"
class X {
  static predicate Test1(i: int)
    // Test1 checks if an int
    // is equal to 1
  { i == 1 }
  // Unrelated trailing comment
  
  // Test2 checks if an int
  // is equal to 2
  static predicate Test2(i: int)
  { i == 2 }
}
", new List<(string nodeTokenValue, string? expectedDocstring)>() {
        ("Test1", "Test1 checks if an int\nis equal to 1"),
        ("Test2", "Test2 checks if an int\nis equal to 2")});
    }

    [Fact]
    public void DocstringWorksForMethodsAndLemmas() {
      DocstringWorksFor(@"
/** ComputeThing prints something to the screen */
method ComputeThing(i: int) returns (j: int)
{ print i; }
// Unattached comment

// Unattached comment
lemma ComputeThing2(i: int) returns (j: int)
  // ComputeThing2 prints something to the screen
  requires i == 2
{ print i; }

// Unattached comment
method ComputeThing3(i: int) returns (j: int)
  // ComputeThing3 prints something to the screen

// Unattached comment
method ComputeThing4(i: int)
  // ComputeThing4 prints something to the screen
  requires i == 2
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("ComputeThing", "ComputeThing prints something to the screen"),
        ("ComputeThing2", "ComputeThing2 prints something to the screen"),
        ("ComputeThing3", "ComputeThing3 prints something to the screen"),
        ("ComputeThing4", "ComputeThing4 prints something to the screen")
      });
    }
    [Fact]
    public void DocstringWorksForConst() {
      DocstringWorksFor(@"
class X {
  const x2 := 29
  // The biggest prime number less than 30

  /** The biggest prime number less than 20 */
  const x1 := 19

  // Unrelated todo 
  const x3 := 37
  // The biggest prime number less than 40
}
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("x1", "The biggest prime number less than 20"),
        ("x2", "The biggest prime number less than 30"),
        ("x3", "The biggest prime number less than 40")});
    }

    [Fact]
    public void DocstringWorksForSubsetType() {
      DocstringWorksFor(@"
type Odd = x: int | x % 2 == 1 witness 1
// Type of numbers that are not divisible by 2 

/** Type of numbers divisible by 2 */
type Even = x: int | x % 2 == 1 witness 1

// Unrelated comment
type Weird = x: int | x % 2 == x % 3 witness 0
// Type of numbers whose remainder modulo 2 or 3 is the same

// Unattached comment
newtype Digit = x: int | 0 <= x < 10
// A single digit

/** A hex digit */
newtype HexDigit = x: int | 0 <= x < 16

newtype BinDigit = x: int | 0 <= x < 2 witness 1
// A binary digit
{
  function flip(): BinDigit {
    1 - this
  }
}

// Unrelated comment
type Weird = x: int | x % 2 == x % 3 witness 0
// Type of numbers whose remainder modulo 2 or 3 is the same


// Unattached comment
type ZeroOrMore = nat
// ZeroOrMore is the same as nat

/** ZeroOrMore2 is the same as nat */ 
type ZeroOrMore2 = nat

// Unattached comment
type OpaqueType
// OpaqueType has opaque methods so you don't see them
{
}

/** OpaqueType2 has opaque methods so you don't see them */
type OpaqueType2
{
}
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("Odd", "Type of numbers that are not divisible by 2"),
        ("Even", "Type of numbers divisible by 2"),
        ("Weird", "Type of numbers whose remainder modulo 2 or 3 is the same"),
        ("Digit", "A single digit"),
        ("HexDigit", "A hex digit"),
        ("BinDigit", "A binary digit"),
        ("ZeroOrMore", "ZeroOrMore is the same as nat"),
        ("ZeroOrMore2", "ZeroOrMore2 is the same as nat"),
        ("OpaqueType", "OpaqueType has opaque methods so you don't see them"),
        ("OpaqueType2", "OpaqueType2 has opaque methods so you don't see them")
      });
    }

    [Fact]
    public void DocstringWorksForDatatypes() {
      DocstringWorksFor(@"
// Unrelated comment
datatype State =
  // A typical log message from a process monitoring
  | // Unrelated comment
    Begin(time: int)
    // The beginning of the process
  | // Unrelated comment
    End(time: int)
    // The end of the process

/** Another typical log message from a process monitoring */
datatype State2 =
  | /** The start of the process */
    Start(time: int)
  | /** The finishing state of the process */
    Finish(time: int)
  | // Not a docstring
    Idle(time: int)
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("State", "A typical log message from a process monitoring"),
        ("Begin", "The beginning of the process"),
        ("End", "The end of the process"),
        ("State2", "Another typical log message from a process monitoring"),
        ("Start", "The start of the process"),
        ("Finish", "The finishing state of the process"),
        ("Idle", null)
      });
    }


    [Fact]
    public void DocstringWorksForClassAndTraits() {
      DocstringWorksFor(@"
trait X
// A typical base class
{}

// Unattached comment
trait T1 extends X
// A typical extending trait
{}

/** A typical extending trait with an even number */
trait T2 extends X
{}

// Unrelated comment
class A extends T
  // A typical example of a class extending a trait
{}

/** Another typical example of a class extending a trait */
class A2 extends T
{}
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("X", "A typical base class"),
        ("T1", "A typical extending trait"),
        ("T2", "A typical extending trait with an even number"),
        ("A", "A typical example of a class extending a trait"),
        ("A2", "Another typical example of a class extending a trait")
      });
    }


    [Fact]
    public void DocstringWorksForExport() {
      DocstringWorksFor(@"
module Test {
  /** You only get the signatures of f and g */
  export hidden provides f
         provides g

  // Unattached comment
  export consistent
    // You get the definition of g but not f
    provides f
    reveals g

  /** You get both the definition of f and g */
  export full provides f
         reveals g

  function g(): int {
    f() + f()
  }
  function f(): int {
    1
  }
}
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("hidden", "You only get the signatures of f and g"),
        ("consistent", "You get the definition of g but not f"),
        ("full", "You get both the definition of f and g")
      });
    }

    [Fact]
    public void DocstringWorksForModules() {
      DocstringWorksFor(@"
// Unattached comment
module A
  // A is the most interesting module
{}

// Unattached comment
module B refines A
  // But it can be refined
{}
// Unattached comment

/** Clearly, modules can be abstract as well */
abstract module C
{}
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("A", "A is the most interesting module"),
        ("B", "But it can be refined"),
        ("C", "Clearly, modules can be abstract as well")
      });
    }

    [Fact]
    public void DocstringWorksForIterators() {
      DocstringWorksFor(@"
/** Iter is interesting */
iterator Iter(x: int) yields (y: int)
  requires A: 0 <= x
{
}

// Unattached comment
iterator Iter2(x: int) yields (y: int)
  // Iter2 is interesting
  requires A: 0 <= x
{
}
", new List<(string nodeTokenValue, string? expectedDocstring)> {
        ("Iter", "Iter is interesting"),
        ("Iter2", "Iter2 is interesting")
      });
    }

    protected Node? FindNode(Node? node, Func<Node, bool> nodeFinder) {
      if (node == null) {
        return node;
      }
      if (nodeFinder(node)) {
        return node;
      } else {
        foreach (var childNode in node.PreResolveChildren) {
          if (FindNode(childNode, nodeFinder) is { } found) {
            return found;
          }
        }

        return null;
      }
    }

    protected void DocstringWorksFor(string source, string nodeTokenValue, string? expectedDocstring) {
      DocstringWorksFor(source, new List<(string nodeTokenValue, string? expectedDocstring)>() {
        (nodeTokenValue, expectedDocstring)
      });
    }

    protected void DocstringWorksFor(string source, List<(string nodeTokenValue, string? expectedDocstring)> tests) {
      var options = DafnyOptions.Create();
      BatchErrorReporter reporter = new BatchErrorReporter(options);
      var newlineTypes = Enum.GetValues(typeof(Newlines));
      foreach (Newlines newLinesType in newlineTypes) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        var programString = AdjustNewlines(source);
        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns(options);
        Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        if (reporter.ErrorCount > 0) {
          var error = reporter.AllMessages[ErrorLevel.Error][0];
          Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
        }

        foreach (var (nodeTokenValue, expectedDocstring) in tests) {
          var targetNode = FindNode(dafnyProgram, node => node.Tok.val == nodeTokenValue);
          if (targetNode == null) {
            Assert.NotNull(targetNode);
          }

          var docString = targetNode.GetDocstring(options);
          Assert.Equal(expectedDocstring, docString);
        }
      }
    }

    private string AdjustNewlines(string programString) {
      return currentNewlines switch {
        Newlines.LF => new Regex("\r?\n").Replace(programString, "\n"),
        Newlines.CR => new Regex("\r?\n").Replace(programString, "\r"),
        _ => new Regex("\r?\n").Replace(programString, "\r\n")
      };
    }
  }
}
