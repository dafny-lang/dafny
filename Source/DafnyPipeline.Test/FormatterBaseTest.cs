#nullable enable
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
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
  public class FormatterBaseTest {
    enum Newlines {
      LF,
      CR,
      CRLF
    };

    private static Regex indentRegex = new Regex(@"(?<=\n|\r(?!\n))[ \t]*");

    private static Regex removeTrailingNewlineRegex = new Regex(@"(?<=\S|\r|\n)[ \t]+(?=\r?\n|\r(?!\n)|$)");

    private Newlines currentNewlines;

    protected void FormatterWorksFor(string testCase, string? expectedProgramString = null, bool expectNoToken = false,
      bool reduceBlockiness = true) {
      BatchErrorReporter reporter = new BatchErrorReporter();
      var options = DafnyOptions.Create();
      DafnyOptions.Install(options);
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

        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns();
        Parser.Parse(programNotIndented, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        if (reporter.ErrorCount > 0) {
          var error = reporter.AllMessages[ErrorLevel.Error][0];
          Assert.False(true, $"{error.message}: line {error.token.line} col {error.token.col}");
        }

        var firstToken = dafnyProgram.GetFirstTopLevelToken();
        if (firstToken == null && !expectNoToken) {
          Assert.False(true, "Did not find a first token");
        }

        var reprinted = firstToken != null && firstToken.line > 0
          ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, reduceBlockiness))
          : programString;
        EnsureEveryTokenIsOwned(programNotIndented, dafnyProgram);
        Assert.Equal(expectedProgram, reprinted);

        // Verify that the formatting is stable.
        module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
        Microsoft.Dafny.Type.ResetScopes();
        builtIns = new BuiltIns();
        Parser.Parse(reprinted, "virtual", "virtual", module, builtIns, reporter);
        dafnyProgram = new Program("programName", module, builtIns, reporter);
        Assert.Equal(0, reporter.ErrorCount);
        firstToken = dafnyProgram.GetFirstTopLevelToken();
        var reprinted2 = firstToken != null && firstToken.line > 0
          ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
            IndentationFormatter.ForProgram(dafnyProgram, reduceBlockiness))
          : reprinted;
        if (reprinted != reprinted2) {
          Console.Write("Double formatting is not stable:\n");
        }
        Assert.Equal(reprinted, reprinted2);
      }
    }

    private void EnsureEveryTokenIsOwned(string programNotIndented, Program dafnyProgram) {
      var firstToken = dafnyProgram.GetFirstTopLevelToken();
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

    private static void ReportNotOwnedToken(string programNotIndented, IToken notOwnedToken, Dictionary<int, List<Node>> posToOwnerNode) {
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

    private static IToken? GetFirstNotOwnedToken(IToken firstToken, HashSet<int> tokensWithoutOwner) {
      IToken? notOwnedToken = firstToken;
      while (notOwnedToken != null && !tokensWithoutOwner.Contains(notOwnedToken.pos)) {
        notOwnedToken = notOwnedToken.Next;
      }

      return notOwnedToken;
    }

    private static HashSet<int> CollectTokensWithoutOwner(Program dafnyProgram, IToken firstToken, out Dictionary<int, List<Node>> posToOwnerNode) {
      HashSet<int> tokensWithoutOwner = new HashSet<int>();
      var posToOwnerNodeInner = new Dictionary<int, List<Node>>();

      var t = firstToken;
      while (t != null) {
        if (t.val != "") {
          tokensWithoutOwner.Add(t.pos);
        }

        t = t.Next;
      }

      void ProcessOwnedTokens(Node node) {
        var ownedTokens = node.OwnedTokens;
        foreach (var token in ownedTokens) {
          tokensWithoutOwner.Remove(token.pos);
          posToOwnerNodeInner.GetOrCreate(token.pos, () => new List<Node>()).Add(node);
        }
      }

      void ProcessNode(Node node) {
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
