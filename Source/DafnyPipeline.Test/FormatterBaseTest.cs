#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
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
  public class FormatterBaseTest {
    private readonly TextWriter output;

    public FormatterBaseTest(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    enum Newlines {
      LF,
      CR,
      CRLF
    };

    private static Regex indentRegex = new Regex(@"(?<=\n|\r(?!\n))[ \t]*");

    private static Regex removeTrailingNewlineRegex = new Regex(@"(?<=\S|\r|\n)[ \t]+(?=\r?\n|\r(?!\n)|$)");

    private Newlines currentNewlines;

    protected async Task FormatterWorksFor(string testCase, string? expectedProgramString = null, bool expectNoToken = false,
      bool reduceBlockiness = true) {
      var options = DafnyOptions.CreateUsingOldParser(output);
      options.DisallowIncludes = true;
      var newlineTypes = Enum.GetValues(typeof(Newlines));
      foreach (Newlines newLinesType in newlineTypes) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        var programString = AdjustNewlines(testCase);
        var programNotIndented = expectedProgramString != null ? programString : indentRegex.Replace(programString, "");
        var expectedProgram = expectedProgramString != null
          ? AdjustNewlines(expectedProgramString)
          : removeTrailingNewlineRegex.Replace(programString, "");

        var uri = new Uri("virtual:virtual");
        var reporter = new BatchErrorReporter(options);
        Microsoft.Dafny.Type.ResetScopes();

        var parseResult = await new ProgramParser().Parse(programNotIndented, uri, reporter);
        var dafnyProgram = parseResult.Program;

        if (reporter.HasErrors) {
          var error = reporter.AllMessagesByLevel[ErrorLevel.Error][0];
          Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
        }

        var firstToken = dafnyProgram.GetFirstTokenForUri(uri);
        if (firstToken == null && !expectNoToken) {
          Assert.False(true, "Did not find a first token");
        }

        var reprinted = firstToken != null && firstToken.line > 0
          ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, firstToken.Uri, reduceBlockiness))
          : programString;
        EnsureEveryTokenIsOwned(uri, programNotIndented, dafnyProgram);
        if (expectedProgram != reprinted) {
          await Console.Out.WriteLineAsync("Formatting after parsing generates an error:");
          Assert.Equal(expectedProgram, reprinted);
        }

        // Formatting should work even if we clone the program after parsing
        Cloner clone = new();
        dafnyProgram.Visit((INode n) => {
          if (n is TopLevelDeclWithMembers nWithMembers) {
            var newMembers = new List<MemberDecl>();
            foreach (var member in nWithMembers.MembersBeforeResolution) {
              newMembers.Add(clone.CloneMember(member, false));
            }

            nWithMembers.MembersBeforeResolution = newMembers.ToImmutableList();
            return false;
          }

          return true;
        });
        var reprintedCloned = firstToken != null && firstToken.line > 0
          ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, firstToken.Uri, reduceBlockiness))
          : programString;
        EnsureEveryTokenIsOwned(uri, programNotIndented, dafnyProgram);
        if (expectedProgram != reprintedCloned) {
          await Console.Out.WriteLineAsync("Formatting after parsing + cloning generates an error:");
          Assert.Equal(expectedProgram, reprinted);
        }

        // Formatting should work after resolution as well.
        DafnyMain.Resolve(dafnyProgram);
        reprinted = firstToken != null && firstToken.line > 0
          ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, firstToken.Uri, reduceBlockiness))
          : programString;
        if (expectedProgram != reprinted) {
          await options.ErrorWriter.WriteLineAsync("Formatting after resolution generates an error:");
          Assert.Equal(expectedProgram, reprinted);
        }

        var initErrorCount = reporter.ErrorCount;

        // Verify that the formatting is stable.
        Microsoft.Dafny.Type.ResetScopes();
        var newReporter = new BatchErrorReporter(options);
        dafnyProgram = (await new ProgramParser().Parse(reprinted, uri, newReporter)).Program;

        Assert.Equal(initErrorCount, reporter.ErrorCount + newReporter.ErrorCount);
        firstToken = dafnyProgram.GetFirstTokenForUri(uri);
        var reprinted2 = firstToken != null && firstToken.line > 0
          ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, firstToken.Uri, reduceBlockiness))
          : reprinted;
        if (reprinted != reprinted2) {
          Console.Write("Double formatting is not stable:\n");
        }

        Assert.Equal(reprinted, reprinted2);
      }
    }

    private void EnsureEveryTokenIsOwned(Uri uri, string programNotIndented, Program dafnyProgram) {
      var firstToken = dafnyProgram.GetFirstTokenForUri(uri);
      if (firstToken == null) {
        return;
      }

      // We compute a set of int instead of a set of tokens because otherwise memory crash occurred
      var tokensWithoutOwner = CollectTokensWithoutOwner(dafnyProgram, firstToken, out var posToOwnerNode);
      if (tokensWithoutOwner.Count == 0) {
        return;
      }

      var notOwnedToken = GetFirstNotOwnedToken(firstToken, tokensWithoutOwner);
      if (notOwnedToken == null) {
        return;
      }

      ReportNotOwnedToken(programNotIndented, notOwnedToken, posToOwnerNode);
    }

    private static void ReportNotOwnedToken(string programNotIndented, IOrigin notOwnedToken,
      Dictionary<int, List<INode>> posToOwnerNode) {
      var nextOwnedToken = notOwnedToken.Next;
      while (nextOwnedToken != null && !posToOwnerNode.ContainsKey(nextOwnedToken.pos)) {
        nextOwnedToken = nextOwnedToken.Next;
      }

      var before = programNotIndented.Substring(0, notOwnedToken.pos);
      var after = programNotIndented.Substring(notOwnedToken.pos + notOwnedToken.val.Length);
      var beforeContextLength = Math.Min(before.Length, 50);
      var wrappedToken = "[[[" + notOwnedToken.val + "]]]";
      var errorString = before.Substring(before.Length - beforeContextLength) + wrappedToken + after;
      errorString = errorString.Substring(0,
        Math.Min(errorString.Length, beforeContextLength + wrappedToken.Length + 50));

      Assert.False(true, $"The token '{notOwnedToken.val}' (L" + notOwnedToken.line + ", C" +
                         (notOwnedToken.col + 1) + ") or (P" + notOwnedToken.pos + ") is not owned:\n" +
                         errorString
      );
    }

    private static IOrigin? GetFirstNotOwnedToken(IOrigin firstToken, HashSet<int> tokensWithoutOwner) {
      IOrigin? notOwnedToken = firstToken;
      while (notOwnedToken != null && !tokensWithoutOwner.Contains(notOwnedToken.pos)) {
        notOwnedToken = notOwnedToken.Next;
      }

      return notOwnedToken;
    }

    private static HashSet<int> CollectTokensWithoutOwner(Program dafnyProgram, IOrigin firstToken,
      out Dictionary<int, List<INode>> posToOwnerNode) {
      HashSet<int> tokensWithoutOwner = new HashSet<int>();
      var posToOwnerNodeInner = new Dictionary<int, List<INode>>();

      var t = firstToken;
      while (t != null) {
        if (t.val != "") {
          tokensWithoutOwner.Add(t.pos);
        }

        t = t.Next;
      }

      void ProcessOwnedTokens(INode node) {
        var ownedTokens = node.OwnedTokens;
        foreach (var token in ownedTokens) {
          tokensWithoutOwner.Remove(token.pos);
          posToOwnerNodeInner.GetOrCreate(token.pos, () => new List<INode>()).Add(node);
        }
      }

      void ProcessNode(INode node) {
        if (node == null) {
          return;
        }

        ProcessOwnedTokens(node);
        foreach (var child in node.PreResolveChildren) {
          ProcessNode(child);
        }
      }

      ProcessNode(dafnyProgram);

      posToOwnerNode = posToOwnerNodeInner;
      return tokensWithoutOwner;
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