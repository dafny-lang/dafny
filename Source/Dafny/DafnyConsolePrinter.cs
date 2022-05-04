using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class DafnyConsolePrinter : ConsolePrinter {
  private readonly Dictionary<string, List<string>> fsCache = new();
  public List<(Implementation, VerificationResult)> VerificationResults { get; } = new();

  private string GetFileLine(string filename, int lineIndex) {
    List<string> lines;
    if (!fsCache.ContainsKey(filename)) {
      try {
        // Note: This is not guaranteed to be the same file that Dafny parsed. To ensure that, Dafny should keep
        // an in-memory version of each file it parses.
        lines = File.ReadLines(filename).ToList();
      } catch (Exception) {
        lines = new List<string>();
      }
      fsCache.Add(filename, lines);
    } else {
      lines = fsCache[filename];
    }
    if (0 <= lineIndex && lineIndex < lines.Count) {
      return lines[lineIndex];
    }
    return "<nonexistent line>";
  }

  private void WriteSourceCodeSnippet(Boogie.IToken tok, TextWriter tw) {
    string line = GetFileLine(tok.filename, tok.line - 1);
    string lineNumber = tok.line.ToString();
    string lineNumberSpaces = new string(' ', lineNumber.Length);
    string columnSpaces = new string(' ', tok.col - 1);
    tw.WriteLine($"{lineNumberSpaces} |");
    tw.WriteLine($"{lineNumber      } | {line}");
    tw.WriteLine($"{lineNumberSpaces} | {columnSpaces}^ here");
    tw.WriteLine("");
  }

  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string category = null) {
    // Dafny has 0-indexed columns, but Boogie counts from 1
    var realigned_tok = new Boogie.Token(tok.line, tok.col - 1);
    realigned_tok.kind = tok.kind;
    realigned_tok.pos = tok.pos;
    realigned_tok.val = tok.val;
    realigned_tok.filename = tok.filename;
    base.ReportBplError(realigned_tok, message, error, tw, category);
    if (DafnyOptions.O.ShowSnippets) {
      WriteSourceCodeSnippet(tok, tw);
    }

    if (tok is Dafny.NestedToken) {
      var nt = (Dafny.NestedToken)tok;
      ReportBplError(nt.Inner, "Related location", false, tw);
    }
  }

  public override void ReportEndVerifyImplementation(Implementation implementation, Boogie.VerificationResult result) {
    VerificationResults.Add((implementation, result));
  }
}
