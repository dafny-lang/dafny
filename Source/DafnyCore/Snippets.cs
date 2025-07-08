using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using DafnyCore.Options;
using Microsoft.Dafny;

namespace DafnyCore;

public class Snippets {
  public static readonly Option<bool> ShowSnippets = new("--show-snippets", () => true,
    "Show a source code snippet for each Dafny message.");

  static Snippets() {
    OptionRegistry.RegisterOption(ShowSnippets, OptionScope.Cli);
  }

  public static void WriteSourceCodeSnippet(DafnyOptions options, TokenRange range, TextWriter tw) {
    var start = range.StartToken;
    var end = range.EndToken;
    string line = GetFileLine(options, range.Uri, start.line - 1);
    if (line == null) {
      return;
    }

    string lineNumber = start.line.ToString();
    string lineNumberSpaces = new string(' ', lineNumber.Length);
    string columnSpaces = new string(' ', start.col - 1);
    var lineStartPos = start.pos - start.col + 1;
    var lineEndPos = lineStartPos + line.Length;

    var tokEndPos = end.pos + end.val.Length;

    var underlineLength = Math.Max(1, Math.Min(tokEndPos - start.pos, lineEndPos - start.pos));
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
        var file = DafnyFile.HandleDafnyFile(OnDiskFileSystem.Instance, new ErrorReporterSink(options), options, uri, Token.NoToken);
        using var reader = file.GetContent().Reader;
        lines = Util.Lines(reader).ToList();
      } catch (Exception) {
        lines = [];
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