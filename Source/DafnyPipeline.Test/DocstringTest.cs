#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Microsoft.Dafny;
using Nerdbank.Streams;
using Xunit;
using Xunit.Abstractions;

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
    private readonly ITestOutputHelper output;

    enum Newlines {
      LF,
      CR,
      CRLF
    };

    public DocstringTest(ITestOutputHelper output) {
      this.output = output;
    }

    private Newlines currentNewlines;

    [Fact]
    public async Task DocStringForAbstractTypeDecl() {
      var programString = @"
// Not docstring
type AB(==) // [START Docstring0 END Docstring0]
// Not docstring

// Not docstring
type AC // [START Docstring1
// END Docstring1]
{
}

/** [START Docstring2 END Docstring2] */
type AD
// Not docstring

// Just a comment because not using the adequate syntax
type NoDocstring3
// Not docstring

// Not docstring
type AF { } // [START Docstring4 END Docstring4]
// Not docstring
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForClassLikeDecl() {
      var programString = @"
// Not docstring
class A { } // [START Docstring0 END Docstring0]
// Not docstring

// Not docstring
class AC // [START Docstring1
// END Docstring1]
{
}

/** [START Docstring2 END Docstring2] */
trait AT {} 
// Just a comment

/** [START Docstring3 END Docstring3] */
trait AT {} // Not a docstring because the syntax above looks more like a docstring
// Just a comment

// Not docstring
class AC2 extends AT // [START Docstring4
// END Docstring4]
{
}

// No docstring
class NoDocstring5 {}
// No docstring

/** [START Docstring6 END Docstring6] */
class AD  {}
// Not docstring
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForDatatypeDecl() {
      var programString = @"
/** [START Docstring0 END Docstring0] */
datatype X = FirstCtor() // [START Docstring1 END Docstring1]
// No docstring

/* No docstring */
datatype Y // [START Docstring2
// END Docstring2]
= 
/** [START Docstring3 END Docstring3] */
SecondCtor()
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForConstVar() {
      var programString = @"
class NoDocstring0 {
  const NoDocstring1: int
  /** [START Docstring2 END Docstring2] */
  const a2: int
  const a3: int /** [START Docstring3 END Docstring3] */
  const a4: int := 5 /** [START Docstring4 END Docstring4] */
  const a5: int
    // [START Docstring5
    // END Docstring5]
  := 5

  var NoDocstring6: int
  /** [START Docstring7 END Docstring7] */
  var a7: int
  var a8: int // [START Docstring8 END Docstring8]
}
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForFunctions() {
      var programString = @"
class NoDocstring0 {
  /** [START Docstring1 END Docstring1] */
  function Test1(): int
  function Test2(): int // [START Docstring2 END Docstring2]
  /** [START Docstring3 END Docstring3] */
  function Test3(): int { 1 } // Not docstring
  function Test4(): int { 2 } // [START Docstring4 END Docstring4]
  /* Not docstring */
  function Test5(): int // [START Docstring5
    // END Docstring5]
  {
    1
  }

  /** [START Docstring6 END Docstring6] */
  function Test6(): (r: int)
  function Test7(): (r: int) // [START Docstring7 END Docstring7]
  /** [START Docstring8 END Docstring8] */
  function Test8(): (r: int) { 1 } // Not docstring
  function Test9(): (r: int) { 2 } // [START Docstring9 END Docstring9]
  /* Not docstring */
  function Test10(): (r: int) // [START Docstring10
    // END Docstring10]
  {
    1
  }
}
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForMethods() {
      var programString = @"
class NoDocstring0 {
  /** [START Docstring1 END Docstring1] */
  method Test1()
  method Test2() // [START Docstring2 END Docstring2]
  /** [START Docstring3 END Docstring3] */
  method Test3() {} // Not docstring
  method Test4() { } // [START Docstring4 END Docstring4]
  /* Just a comment */
  method Test5() // [START Docstring5
    // END Docstring5]
  {
  }

  /** [START Docstring6 END Docstring6] */
  method Test6() returns (r: int)
  method Test7() returns (r: int) // [START Docstring7 END Docstring7]
  /** [START Docstring8 END Docstring8] */
  method Test8() returns (r: int) { } // Not docstring
  method Test9() returns (r: int) { } // [START Docstring9 END Docstring9]
  /* Not docstring */
  method Test10() returns (r: int) // [START Docstring10
    // END Docstring10]
  {
  }
}
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForIterators() {
      var programString = @"
/** [START Docstring0 END Docstring0] */
iterator Gen(start: int) yields (x: int) // Just a comment
  yield ensures true
{}

/* Just a comment */
iterator Gen(start: int) yields (x: int) //  [START Docstring1 END Docstring1]
  yield ensures true
{}

/* Just a comment */
iterator Gen(start: int) yields (x: int)
  yield ensures true
{} //  [START Docstring2 END Docstring2]
// Just a comment
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForModules() {
      var programString = @"
/** [START Docstring0 END Docstring0] */
module Module0 {
  // No docstring for this module
  module NoDocstring1 {}
  module Module2 {} // [START Docstring2 END Docstring2]
  /** [START Docstring3 END Docstring3] */
  module Module3 {} // Not docstring

  module Test4 refines Else // [START Docstring4
  // END Docstring4]
  {
  }
}
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForExportSets() {
      var programString = @"
module NoDocstring0 {
  /** [START Docstring1 END Docstring1] */
  export provides A, B, C

  // Just a comment
  export
    // [START Docstring2 END Docstring2]
    provides D, E, F

  // Just a comment
  export All
    // [START Docstring3 END Docstring3]
    provides D, E

  // Just a comment
  export AllBis
    provides D, E // [START Docstring4 END Docstring4]
  // Just a comment
}";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForNewtypes() {
      var programString = @"
/** [START Docstring0 END Docstring0] */
newtype Int0 = x: int | true // Not docstring

newtype Int1 = x: int | true { predicate NoDocstring2() { x == 0 } } // [START Docstring1 END Docstring1]

/** [START Docstring3 END Docstring3] */
newtype Int3 = x: int | true { predicate NoDocstring4() { x == 0 } } // Not docstring

/* Not docstring */
newtype Int5
  // [START Docstring5
  // END Docstring5]
= x: int | true // Not docstring

newtype Int6 = x: int | true witness 0 // [START Docstring6 END Docstring6]
";
      await TestAllDocstrings(programString);
    }

    [Fact]
    public async Task DocStringForSynonymTypes() {
      var programString = @"
/** [START Docstring0 END Docstring0] */
type Int0 = x: int | true // Not docstring

type Int1 = x: int | true witness 0 // [START Docstring1 END Docstring1]

/** [START Docstring2 END Docstring2] */
type Int2 = x: int | true // Not docstring

/* Not docstring */
type Int3
  // [START Docstring3
  // END Docstring3]
= x: int | true // Not docstring
";
      await TestAllDocstrings(programString);
    }

    private async Task TestAllDocstrings(string programString) {
      var options = DafnyOptions.CreateUsingOldParser(new BufferTextWriter());
      foreach (Newlines newLinesType in Enum.GetValues(typeof(Newlines))) {
        currentNewlines = newLinesType;
        programString = AdjustNewlines(programString);

        var reporter = new BatchErrorReporter(options);
        var dafnyProgram = await Utils.Parse(reporter, programString, false);
        if (reporter.ErrorCount != 0) {
          throw new Exception(reporter.AllMessagesByLevel[ErrorLevel.Error][0].ToString());
        }
        Assert.Equal(0, reporter.ErrorCount);
        var topLevelDecls = dafnyProgram.DefaultModuleDef.TopLevelDecls.ToList();
        var hasDocString = topLevelDecls.OfType<IHasDocstring>().SelectMany(i => {
          var result = new List<IHasDocstring> { i };
          if (i is DatatypeDecl d) {
            foreach (var ctor in d.Ctors) {
              result.Add(ctor);
            }
          }

          if (i is TopLevelDeclWithMembers memberContainer) {
            foreach (var member in memberContainer.Members) {
              if (member is IHasDocstring hasDocstring) {
                result.Add(hasDocstring);
              }
            }
          }

          if (i is LiteralModuleDecl modDecl) {
            foreach (var innerDecl in modDecl.ModuleDef.TopLevelDecls) {
              if (innerDecl is IHasDocstring hasDocstring) {
                result.Add(hasDocstring);
              }
            }
          }

          return result;
        }).ToList();
        var matches = new Regex($@"Docstring(\d+)").Matches(programString);
        var highestDocstringIndex = 0;
        for (var i = 0; i < matches.Count; i++) {
          var match = matches[i];
          var index = int.Parse(match.Groups[1].Value);
          if (index > highestDocstringIndex) {
            highestDocstringIndex = index;
          }
        }

        Assert.Equal(hasDocString.Count - 1, highestDocstringIndex);
        for (var i = 0; i < hasDocString.Count; i++) {
          var iHasDocString = hasDocString[i];
          var triviaWithDocstring = AdjustNewlines(iHasDocString.GetTriviaContainingDocstring() ?? "");
          if (!(new Regex($@"\[START Docstring{i}[\s\S]*END Docstring{i}\]")).IsMatch(triviaWithDocstring)) {
            if (iHasDocString is Declaration decl && decl.Name.Contains("NoDocstring")) {
              // OK
            } else {
              Assert.True(false, $"\"[START Docstring{i}...END Docstring{i}]\" not found in {triviaWithDocstring}");
            }
          } else {
            Assert.Equal(triviaWithDocstring.Trim(), triviaWithDocstring);
          }
        }
      }
    }

    [Fact]
    async Task DocstringWorksForPredicates() {
      await DocstringWorksFor(@"
predicate p1()
  // Always true. Every time.
  ensures p1() == true
{ true }

predicate p2(): (y: bool)
  // Always true.
  ensures y == true
{ true }

predicate p3(): (y: bool)
  // Always true every time.
  ensures y == true
", [
        ("p1", "Always true. Every time."),
        ("p2", "Always true."),
        ("p3", "Always true every time.")
      ]);
    }
    [Fact]
    public async Task DocstringWorksForFunctions() {
      await DocstringWorksFor(@"
function Test1(i: int): int
  // Test1 computes an int
  // It takes an int and adds 1 to it
{ i + 1 }

function Test2(i: int): int
  //Test2 computes an int
  //It takes an int and adds 2 to it
{ i + 2 }
// Trailing comment

/** Test3 computes an int
  * It takes an int and adds 3 to it */
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

function Test6(i: int): int /**
  * Test6 computes an int
  * It takes an int and adds 6 to it */

function Test7(i: int): (j: int)
  /* Test7 computes an int
  It takes an int and adds 7 to it */
{ i + 7 }

function Test8(i: int): int
  /* Test8 computes an int
   * It takes an int and adds 8 to it */
{ i + 8 }

function Test9(i: int): int /*
  Test9 computes an int
  It takes an int and adds 9 to it */
{ i + 9 }

function Test10(i: int): int
  /* Test10 computes an int
    *  It takes an int and adds 10 to it */
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
    public async Task DocstringWorksForPredicate() {
      await DocstringWorksFor(@"
class X {
  static predicate Test1(i: int)
    // Test1 checks if an int
    // is equal to 1
  { i == 1 }
  // Unrelated trailing comment
  
  /** Test2 checks if an int
    * is equal to 2 */
  static predicate Test2(i: int)
  { i == 2 }
}
", [
        ("Test1", "Test1 checks if an int\nis equal to 1"),
        ("Test2", "Test2 checks if an int\nis equal to 2")
      ]);
    }

    [Fact]
    public async Task DocstringWorksForMethodsAndLemmas() {
      await DocstringWorksFor(@"
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
method ComputeThing3(i: int) returns (j: int) /*
  ComputeThing3 prints something to the screen */

// Unattached comment
method ComputeThing4(i: int)
  // ComputeThing4 prints something to the screen
  requires i == 2
", [
        ("ComputeThing", "ComputeThing prints something to the screen"),
        ("ComputeThing2", "ComputeThing2 prints something to the screen"),
        ("ComputeThing3", "ComputeThing3 prints something to the screen"),
        ("ComputeThing4", "ComputeThing4 prints something to the screen")
      ]);
    }
    [Fact]
    public async Task DocstringWorksForConst() {
      await DocstringWorksFor(@"
class X {
  const x2 := 29 // The biggest prime number less than 30

  /** The biggest prime number less than 20 */
  const x1 := 19

  // Unrelated todo 
  const x3 := 37 // The biggest prime number less than 40
}
", [
        ("x1", "The biggest prime number less than 20"),
        ("x2", "The biggest prime number less than 30"),
        ("x3", "The biggest prime number less than 40")
      ]);
    }

    [Fact]
    public async Task DocstringWorksForSubsetType() {
      await DocstringWorksFor(@"
type Odd = x: int | x % 2 == 1 witness 1 // Type of numbers that are not divisible by 2 

/** Type of numbers divisible by 2 */
type Even = x: int | x % 2 == 1 witness 1

// Unrelated comment
type Weird = x: int | x % 2 == x % 3 witness 0 // Type of numbers whose remainder modulo 2 or 3 is the same

// Unattached comment
newtype Digit = x: int | 0 <= x < 10 // A single digit

/** A hex digit */
newtype HexDigit = x: int | 0 <= x < 16

newtype BinDigit
  // A binary digit
  = x: int | 0 <= x < 2 witness 1
{
  function flip(): BinDigit {
    1 - this
  }
}

// Unrelated comment
type Weird = x: int | x % 2 == x % 3 witness 0 // Type of numbers whose remainder modulo 2 or 3 is the same

// Unattached comment
type ZeroOrMore = nat // ZeroOrMore is the same as nat

/** ZeroOrMore2 is the same as nat */ 
type ZeroOrMore2 = nat

// Unattached comment
type AbstractType
// AbstractType has opaque methods so you don't see them
{
}

/** AbstractType2 has opaque methods so you don't see them */
type AbstractType2
{
}
", [
        ("Odd", "Type of numbers that are not divisible by 2"),
        ("Even", "Type of numbers divisible by 2"),
        ("Weird", "Type of numbers whose remainder modulo 2 or 3 is the same"),
        ("Digit", "A single digit"),
        ("HexDigit", "A hex digit"),
        ("BinDigit", "A binary digit"),
        ("ZeroOrMore", "ZeroOrMore is the same as nat"),
        ("ZeroOrMore2", "ZeroOrMore2 is the same as nat"),
        ("AbstractType", "AbstractType has opaque methods so you don't see them"),
        ("AbstractType2", "AbstractType2 has opaque methods so you don't see them")
      ]);
    }

    [Fact]
    public async Task DocstringWorksForDatatypes() {
      await DocstringWorksFor(@"
// Unrelated comment
datatype State
  // A typical log message from a process monitoring
  = // Unrelated comment
    Begin(time: int) // The beginning of the process
  | // Unrelated comment
    End(time: int) // The end of the process

/** Another typical log message from a process monitoring */
datatype State2 =
  | /** The start of the process */
    Start(time: int)
  | /** The finishing state of the process */
    Finish(time: int)
  | // Not a docstring
    Idle(time: int)
", [
        ("State", "A typical log message from a process monitoring"),
        ("Begin", "The beginning of the process"),
        ("End", "The end of the process"),
        ("State2", "Another typical log message from a process monitoring"),
        ("Start", "The start of the process"),
        ("Finish", "The finishing state of the process"),
        ("Idle", null)
      ]);
    }


    [Fact]
    public async Task DocstringWorksForClassAndTraits() {
      await DocstringWorksFor(@"
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
", [
        ("X", "A typical base class"),
        ("T1", "A typical extending trait"),
        ("T2", "A typical extending trait with an even number"),
        ("A", "A typical example of a class extending a trait"),
        ("A2", "Another typical example of a class extending a trait")
      ]);
    }


    [Fact]
    public async Task DocstringWorksForExport() {
      await DocstringWorksFor(@"
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
", [
        ("hidden", "You only get the signatures of f and g"),
        ("consistent", "You get the definition of g but not f"),
        ("full", "You get both the definition of f and g")
      ]);
    }

    [Fact]
    public async Task DocstringWorksForModules() {
      await DocstringWorksFor(@"
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
", [
        ("A", "A is the most interesting module"),
        ("B", "But it can be refined"),
        ("C", "Clearly, modules can be abstract as well")
      ]);
    }

    [Fact]
    public async Task DocstringWorksForIterators() {
      await DocstringWorksFor(@"
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
", [
        ("Iter", "Iter is interesting"),
        ("Iter2", "Iter2 is interesting")
      ]);
    }

    protected INode? FindNode(INode? node, Func<INode, bool> nodeFinder) {
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

    protected Task DocstringWorksFor(string source, string nodeTokenValue, string? expectedDocstring) {
      return DocstringWorksFor(source, [(nodeTokenValue, expectedDocstring)]);
    }

    protected async Task DocstringWorksFor(string source, List<(string nodeTokenValue, string? expectedDocstring)> tests) {
      var options = DafnyOptions.CreateUsingOldParser((TextWriter)new WriterFromOutputHelper(output));
      var newlineTypes = Enum.GetValues(typeof(Newlines));
      foreach (Newlines newLinesType in newlineTypes) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        var programString = AdjustNewlines(source);

        var reporter = new BatchErrorReporter(options);
        var dafnyProgram = await Utils.Parse(reporter, programString, false);
        if (reporter.HasErrors) {
          var error = reporter.AllMessagesByLevel[ErrorLevel.Error][0];
          Assert.False(true, $"{error.Message}: line {error.Range.StartToken.line} col {error.Range.StartToken.col}");
        }

        foreach (var (nodeTokenValue, expectedDocstring) in tests) {
          var targetNode = FindNode(dafnyProgram, node => node.Origin.val == nodeTokenValue);
          if (targetNode == null) {
            Assert.NotNull(targetNode);
          }

          var docString = ((IHasDocstring)targetNode).GetDocstring(options);
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