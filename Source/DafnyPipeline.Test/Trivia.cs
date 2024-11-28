using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Trivia")]
  public class Trivia {

    private readonly TextWriter output;

    public Trivia(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    enum Newlines { LF, CR, CRLF };

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

/** No docstring */
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
  /** Not docstring because docstring in precise place */
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
  /** Not docstring because docstring in precise place */
  function Test10(): (r: int) // [START Docstring10
    // END Docstring10]
  {
    1
  }
}
";
      await TestAllDocstrings(programString);
    }


    private async Task TestAllDocstrings(string programString)
    {
      var options = DafnyOptions.CreateUsingOldParser(output);
      foreach (Newlines newLinesType in Enum.GetValues(typeof(Newlines))) {
        currentNewlines = newLinesType;
        programString = AdjustNewlines(programString);

        var reporter = new BatchErrorReporter(options);
        var dafnyProgram = await Utils.Parse(reporter, programString, false);
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
        for(var i = 0; i < hasDocString.Count; i++) {
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
    public async Task TriviaSplitWorksOnLinuxMacAndWindows() {
      var options = DafnyOptions.CreateUsingOldParser(output);
      foreach (Newlines newLinesType in Enum.GetValues(typeof(Newlines))) {
        currentNewlines = newLinesType;
        var programString = @"
// Comment ∈ before
module Test // Module docstring
{} // Attached to }

/** Trait docstring */
trait Trait1 { }

// Just a comment
trait Trait2 extends Trait1
// Trait docstring
{ }
// This is attached to trait2
// This is also attached to trait2

// This is attached to n
type n = x: int | x % 2 == 0
// This is attached to n as well

// Just a comment
class Class1 extends Trait1
// Class docstring
{ }
// This is attached to the class

// Comment attached to c
const c := 2;
// Docstring attached to c

// This is attached to f
function f(): int
// This is f docstring
ensures true
{ 1 }

/** This is the docstring */
function g(): int
// This is not the docstring
ensures true
{ 1 }

// Just a regular comment
method m() returns (r: int)
// This is the docstring
ensures true
{ assert true; }
";
        programString = AdjustNewlines(programString);

        var reporter = new BatchErrorReporter(options);
        var dafnyProgram = await Utils.Parse(reporter, programString, false);
        Assert.Equal(0, reporter.ErrorCount);
        var topLevelDecls = dafnyProgram.DefaultModuleDef.TopLevelDecls.ToList();
        Assert.Equal(6, topLevelDecls.Count());
        var defaultClass = topLevelDecls.OfType<DefaultClassDecl>().First();
        var moduleTest = topLevelDecls[1] as LiteralModuleDecl;
        var trait1 = topLevelDecls[2];
        var trait2 = topLevelDecls[3];
        var subsetType = topLevelDecls[4];
        var class1 = topLevelDecls[5] as ClassDecl;
        Assert.NotNull(moduleTest);
        Assert.NotNull(class1);
        Assert.NotNull(defaultClass);
        Assert.Equal(4, defaultClass.Members.Count);
        var c = defaultClass.Members[0];
        var f = defaultClass.Members[1];
        var g = defaultClass.Members[2];
        var m = defaultClass.Members[3];
        Assert.NotNull(trait1.StartToken.Next);
        Assert.Equal("Trait1", trait1.StartToken.Next.val);

        AssertTrivia(moduleTest, "\n// Comment ∈ before\n", " // Module docstring\n");
        AssertTrivia(trait1, "/** Trait docstring */\n", " ");
        AssertTrivia(trait2, "// Just a comment\n", "\n// Trait docstring\n");
        AssertTrivia(subsetType, "// This is attached to n\n", "\n// This is attached to n as well\n\n");
        AssertTrivia(class1, "// Just a comment\n", "\n// Class docstring\n");
        AssertTrivia(c, "// Comment attached to c\n", "\n// Docstring attached to c\n\n");
        AssertTrivia(f, "// This is attached to f\n", "\n// This is f docstring\n");
        AssertTrivia(g, "/** This is the docstring */\n", "\n// This is not the docstring\n");
        AssertTrivia(m, "// Just a regular comment\n", "\n// This is the docstring\n");

        TestTokens(dafnyProgram);
      }
    }

    // Asserts that a token is owned by at most one node
    // and that every token from start to end of every program child
    // is owned by a node.
    private void TestTokens(Node program) {
      var allTokens = new HashSet<IToken>();

      void Traverse(INode node) {
        foreach (var ownedToken in node.OwnedTokens) {
          Assert.DoesNotContain(ownedToken, allTokens);
          allTokens.Add(ownedToken);
        }
        foreach (var child in node.PreResolveChildren) {
          Traverse(child);
        }
      }

      Traverse(program);

      void AreAllTokensOwned(INode node) {
        if (node.StartToken is { filename: { } }) {
          var t = node.StartToken;
          while (t != null && t != node.EndToken) {
            Assert.Contains(t, allTokens);
            t = t.Next;
          }
        } else {
          foreach (var child in node.PreResolveChildren) {
            AreAllTokensOwned(child);
          }
        }
      }

      AreAllTokensOwned(program);
    }

    private string AdjustNewlines(string programString) {
      return currentNewlines switch {
        Newlines.LF => new Regex("\r?\n").Replace(programString, "\n"),
        Newlines.CR => new Regex("\r?\n").Replace(programString, "\r"),
        _ => new Regex("\r?\n").Replace(programString, "\r\n")
      };
    }

    private void AssertTrivia(Node topLevelDecl, string triviaBefore, string triviaDoc) {
      Assert.Equal(AdjustNewlines(triviaBefore), topLevelDecl.StartToken.LeadingTrivia);
      if (topLevelDecl is IHasDocstring hasDocstring) {
        Assert.Equal(AdjustNewlines(triviaDoc), hasDocstring.GetTriviaContainingDocstring());
      } else {
        Assert.True(false);
      }
    }
  }
}
