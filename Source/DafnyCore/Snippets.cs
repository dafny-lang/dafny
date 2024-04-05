using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.Dafny;

namespace DafnyCore;

public class Snippets {
  public static readonly Option<bool> ShowSnippets = new("--show-snippets", () => true,
    "Show a source code snippet for each Dafny message.");

  static Snippets() {
    DooFile.RegisterNoChecksNeeded(ShowSnippets);
  }

  public static void WriteSourceCodeSnippet(DafnyOptions options, IToken tok, TextWriter tw) {
    string line = GetFileLine(options, tok.Uri, tok.line - 1);
    if (line == null) {
      return;
    }

    string lineNumber = tok.line.ToString();
    string lineNumberSpaces = new string(' ', lineNumber.Length);
    string columnSpaces = new string(' ', tok.col - 1);
    var lineStartPos = tok.pos - tok.col + 1;
    var lineEndPos = lineStartPos + line.Length;

    var tokEndPos = tok.pos + tok.val.Length;
    if (tok is RangeToken rangeToken) {
      tokEndPos = rangeToken.EndToken.pos + rangeToken.EndToken.val.Length;
    }
    var underlineLength = Math.Max(1, Math.Min(tokEndPos - tok.pos, lineEndPos - tok.pos));
    string underline = new string('^', underlineLength);
    tw.WriteLine($"{lineNumberSpaces} |");
    tw.WriteLine($"{lineNumber} | {line}");
    tw.WriteLine($"{lineNumberSpaces} | {columnSpaces}{underline}");
    tw.WriteLine("");
  }

  private static string GetFileLine(DafnyOptions options, Uri uri, int lineIndex) {
    var fsCache = FsCaches.GetOrCreateValue(options)!;
    List<string> lines = fsCache.GetOrAdd(uri, key => {
      try {
        // Note: This is not guaranteed to be the same file that Dafny parsed. To ensure that, Dafny should keep
        // an in-memory version of each file it parses.
#pragma warning disable VSTHRD002
        var file = DafnyFile.CreateAndValidate(new ErrorReporterSink(options), OnDiskFileSystem.Instance, options, uri, Token.NoToken).Result;
#pragma warning restore VSTHRD002
        using var reader = file.GetContent();
        lines = Util.Lines(reader).ToList();
      } catch (Exception) {
        lines = new List<string>();
      }
      return lines;
    });
    if (0 <= lineIndex && lineIndex < lines.Count) {
      return lines[lineIndex];
    }
    return null;
  }

  private static readonly ConditionalWeakTable<DafnyOptions, ConcurrentDictionary<Uri, List<string>>> FsCaches = new();
}