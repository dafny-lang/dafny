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
{ } /*
This is attached to trait2
This is also attached to trait2 */

// This is attached to n
type n = x: int | x % 2 == 0 // This docstring is attached to n

// Just a comment
class Class1 extends Trait1
// Class docstring
{ } // This is attached to the class

// Comment attached to c
const c := 2 // Docstring attached to c

// This is attached to f
function f(): int // This is f docstring
ensures true
{ 1 }

/** This is the docstring */
function g(): int // This is not the docstring
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

        AssertTrivia(moduleTest, "\n// Comment ∈ before\n", "// Module docstring");
        AssertTrivia(trait1, "\n/** Trait docstring */\n", "/** Trait docstring */");
        AssertTrivia(trait2, "\n// Just a comment\n", "// Trait docstring");
        AssertTrivia(subsetType, "\n\n// This is attached to n\n", "// This docstring is attached to n");
        AssertTrivia(class1, "\n// Just a comment\n", "// Class docstring");
        AssertTrivia(c, "\n// Comment attached to c\n", "// Docstring attached to c");
        AssertTrivia(f, "\n// This is attached to f\n", "// This is f docstring");
        AssertTrivia(g, "\n/** This is the docstring */\n", "/** This is the docstring */");
        AssertTrivia(m, "\n// Just a regular comment\n", "// This is the docstring");

        TestTokens(dafnyProgram);
      }
    }

    // Asserts that a token is owned by at most one node
    // and that every token from start to end of every program child
    // is owned by a node.
    private void TestTokens(Node program) {
      var allTokens = new HashSet<IOrigin>();

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
