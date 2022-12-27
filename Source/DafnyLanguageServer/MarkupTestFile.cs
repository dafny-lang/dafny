// Modified after being taken from https://github.com/dotnet/roslyn/blob/576abfa9a8f2d64967ceabe7fa0e5b7ebe550752/src/Compilers/Test/Core/MarkedSource/MarkupTestFile.cs
// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
// See the LICENSE file in the project root for more information.

#nullable disable

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Security.Policy;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis.Text;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer {
  /// <summary>
  /// To aid with testing, we define a special type of text file that can encode additional
  /// information in it.  This prevents a test writer from having to carry around multiple sources
  /// of information that must be reconstituted.  For example, instead of having to keep around the
  /// contents of a file *and* and the location of the cursor, the tester can just provide a
  /// string with the "><" string in it.  This allows for easy creation of "FIT" tests where all
  /// that needs to be provided are strings that encode every bit of state necessary in the string
  /// itself.
  /// 
  /// The current set of encoded features we support are: 
  /// 
  /// >< - The position in the file.  There can be at most one of these.
  /// 
  /// [> ... <] - A span of text in the file.  There can be many of these and they can be nested
  /// and/or overlap the $ position.
  /// 
  /// {>Name: ... <} A span of text in the file annotated with an identifier.  There can be many of
  /// these, including ones with the same name.
  /// 
  /// Additional encoded features can be added on a case by case basis.
  /// </summary>
  public static class MarkupTestFile {
    private const string SpanStartString = "[>";
    private const string SpanEndString = "<]";

    private static void Parse(string input, out string output, out List<int> positions,
      out IDictionary<string, List<TextSpan>> spans) {
      positions = new List<int>();
      var tempSpans = new Dictionary<string, List<TextSpan>>();

      var outputBuilder = new StringBuilder();

      // A stack of span starts along with their associated annotation name.  [><] spans simply
      // have empty string for their annotation name.
      var spanStartStack = new Stack<(int matchIndex, string name)>();
      var namedSpanStartStack = new Stack<(int matchIndex, string name)>();

      var r = new Regex(@"(?<Position>><)|(?<SpanStart>\[>)|(?<SpanEnd><\])|(?<NameSpanStart>\{>([-_.A-Za-z0-9\+]+)\:)|(?<NameSpanEnd><\})");
      var outputIndex = 0;
      var inputIndex = 0;
      foreach (Match match in r.Matches(input)) {
        var diff = inputIndex - outputIndex;
        var matchIndexInOutput = match.Index - diff;
        var outputPart = input.Substring(inputIndex, match.Index - inputIndex);
        outputIndex += outputPart.Length;
        outputBuilder.Append(outputPart);
        inputIndex = match.Index + match.Length;
        if (match.Groups["Position"].Success) {
          positions.Add(matchIndexInOutput);
        } else if (match.Groups["SpanStart"].Success) {
          spanStartStack.Push((matchIndexInOutput, string.Empty));
        } else if (match.Groups["NameSpanStart"].Success) {
          namedSpanStartStack.Push((matchIndexInOutput, string.Empty));
        } else if (match.Groups["SpanEnd"].Success) {
          PopSpan(spanStartStack, tempSpans, matchIndexInOutput);
        } else if (match.Groups["NameSpanEnd"].Success) {
          PopSpan(namedSpanStartStack, tempSpans, matchIndexInOutput);
        }
      }


      if (spanStartStack.Count > 0) {
        throw new ArgumentException($"Saw {SpanStartString} without matching {SpanEndString}");
      }

      if (namedSpanStartStack.Count > 0) {
        throw new ArgumentException(@"Saw '{<' without matching '>}'");
      }

      // Append the remainder of the string.
      outputBuilder.Append(input.Substring(inputIndex));
      output = outputBuilder.ToString();
      spans = tempSpans.ToDictionary(kvp => kvp.Key, kvp => kvp.Value);
    }

    private static void PopSpan(
        Stack<(int matchIndex, string name)> spanStartStack,
        IDictionary<string, List<TextSpan>> spans,
        int finalIndex) {
      var (matchIndex, name) = spanStartStack.Pop();

      var span = TextSpan.FromBounds(matchIndex, finalIndex);
      spans.GetOrCreate(name, () => new List<TextSpan>()).Add(span);
    }

    private static void AddMatch(string input, string value, int currentIndex, List<(int, string)> matches) {
      var index = input.IndexOf(value, currentIndex, StringComparison.Ordinal);
      if (index >= 0) {
        matches.Add((index, value));
      }
    }

    private static void GetIndexAndSpans(
        string input, out string output, out List<int> positions, out ImmutableArray<TextSpan> spans) {
      Parse(input, out output, out positions, out var dictionary);

      var builder = dictionary.GetOrCreate(string.Empty, () => new List<TextSpan>());
      builder.Sort((left, right) => left.Start - right.Start);
      spans = builder.ToImmutableArray();
    }

    public static void GetIndexAndSpans(
        string input, out string output, out List<int> positions, out IDictionary<string, ImmutableArray<TextSpan>> spans) {
      Parse(input, out output, out positions, out var dictionary);
      spans = dictionary.ToDictionary(kvp => kvp.Key, kvp => kvp.Value.ToImmutableArray());
    }

    public static void GetSpans(string input, out string output, out IDictionary<string, ImmutableArray<TextSpan>> spans)
        => GetIndexAndSpans(input, out output, out var cursorPositionOpt, out spans);

    public static void GetPositionAndRange(string input, out string output, out Position position, out Range range) {
      GetPositionAndRanges(input, out output, out position, out var resultRanges);
      range = resultRanges.Single();
    }

    public static void GetPositionsAndNamedRanges(string input, out string output, out IList<Position> positions,
      out IDictionary<string, ImmutableArray<Range>> ranges) {
      GetIndexAndSpans(input, out output, out var positionIndices, out IDictionary<string, ImmutableArray<TextSpan>> spans);
      var buffer = new TextBuffer(output);
      positions = positionIndices.Select(index => buffer.FromIndex(index)).ToList();
      ranges = spans.ToDictionary(span => span.Key,
        span => span.Value.Select(s =>
          new Range(buffer.FromIndex(s.Start), buffer.FromIndex(s.End))).ToImmutableArray());
    }

    public static void GetPositionsAndRanges(string input, out string output, out IList<Position> positions, out ImmutableArray<Range> ranges) {
      GetIndexAndSpans(input, out output, out var positionIndices, out ImmutableArray<TextSpan> spans);
      var buffer = new TextBuffer(output);
      positions = positionIndices.Select(index => buffer.FromIndex(index)).ToList();
      ranges = spans.Select(span => new Range(buffer.FromIndex(span.Start), buffer.FromIndex(span.End)))
        .ToImmutableArray();
    }

    public static void GetPositionAndRanges(string input, out string output, out Position cursorPosition, out ImmutableArray<Range> ranges) {
      GetPositionsAndRanges(input, out output, out var positions, out ranges);
      cursorPosition = positions.Single();
    }

    public static void GetPosition(string input, out string output, out List<int> positions)
        => GetIndexAndSpans(input, out output, out positions, out ImmutableArray<TextSpan> spans);

    public static void GetPositionAndSpan(string input, out string output, out List<int> positions, out TextSpan textSpan) {
      GetIndexAndSpans(input, out output, out positions, out ImmutableArray<TextSpan> spans);
      textSpan = spans.Single();
    }

    public static void GetSpans(string input, out string output, out ImmutableArray<TextSpan> spans) {
      GetIndexAndSpans(input, out output, out var pos, out spans);
    }

    public static void GetSpan(string input, out string output, out TextSpan textSpan) {
      GetSpans(input, out output, out ImmutableArray<TextSpan> spans);
      textSpan = spans.Single();
    }
  }
}
