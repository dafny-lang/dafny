using System;
using System.Collections.Generic;
using System.Linq;
using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class TextBuffer {
  public string Text { get; }

  private readonly IIntervalTree<int, BufferLine> indexToLineTree = new IntervalTree<int, BufferLine>();
  public readonly IReadOnlyList<BufferLine> Lines;

  private TextBuffer(string text, IReadOnlyList<BufferLine> lines) {
    Text = text;
    Lines = lines;

    foreach (var lineInfo in lines) {
      indexToLineTree.Add(lineInfo.StartIndex, lineInfo.EndIndex, lineInfo);
    }
  }

  public TextBuffer(string text) : this(text, ComputeLines(text, 0, 0, text.Length)) { }

  private static List<BufferLine> ComputeLines(string text, int lineIndexStart, int startIndex, int endIndex) {
    var lines = new List<BufferLine>();
    var index = startIndex;
    for (; index < text.Length;) {
      if (text[index] == '\n') {
        lines.Add(new BufferLine(lineIndexStart + lines.Count, startIndex, index));
        index += 1;
        startIndex = index;
        if (index > endIndex) {
          return lines;
        }
      } else if (text.Length > index + 1 && text.Substring(index, 2) == "\r\n") {
        lines.Add(new BufferLine(lineIndexStart + lines.Count, startIndex, index));
        index += 2;
        startIndex = index;
        if (index > endIndex) {
          return lines;
        }
      } else {
        index += 1;
      }
    }

    lines.Add(new BufferLine(lineIndexStart + lines.Count, startIndex, index));
    return lines;
  }

  public Position FromIndex(int index) {
    var line = IndexToLine(index);
    return new Position(line.LineNumber, index - line.StartIndex);
  }

  private BufferLine IndexToLine(int index) {
    return indexToLineTree.Query(index).Single();
  }

  public int ToIndex(Position position) {
    return Lines[position.Line].StartIndex + position.Character;
  }

  public TextBuffer ApplyTextChange(TextDocumentContentChangeEvent change) {
    if (change.Range == null) {
      // https://microsoft.github.io/language-server-protocol/specifications/specification-3-17/#textDocumentContentChangeEvent
      return new TextBuffer(change.Text);
    }

    int startIndex = ToIndex(change.Range.Start);
    int endIndex = ToIndex(change.Range.End);
    var newText = Text[..startIndex] + change.Text + Text[endIndex..];
    // TODO: To reinstate this optimization, we need to prove its equivalence.
    // Otherwise, bugs have been found (e.g. https://github.com/dafny-lang/dafny/issues/2890)
    /*var changeStartLine = IndexToLine(startIndex);
    var changeEndLine = IndexToLine(endIndex);

    var indexDelta = newText.Length - Text.Length;
    var freshLines = ComputeLines(newText, changeStartLine.LineNumber, changeStartLine.StartIndex, changeStartLine.EndIndex + indexDelta);
    var lineDelta = freshLines.Count - (changeEndLine.LineNumber - changeStartLine.LineNumber + 1);
    var migratedLinesAfterChange =
      Lines.Skip(1 + changeEndLine.LineNumber).
      Select(line => new BufferLine(
        line.LineNumber + lineDelta,
        line.StartIndex + indexDelta,
        line.EndIndex + indexDelta));
    var newTotalLines = Lines.Take(changeStartLine.LineNumber).Concat(freshLines).Concat(migratedLinesAfterChange).ToList();*/
    var newTotalLines = ComputeLines(newText, 0, 0, newText.Length);
    return new TextBuffer(newText, newTotalLines);
  }

  public string Extract(Range range) {
    var start = ToIndex(range.Start);
    var end = ToIndex(range.End);
    var length = end - start;
    if (end < start) {
      throw new ArgumentException();
    }
    if (start < 0 || end >= Text.Length) {
      throw new ArgumentOutOfRangeException();
    }

    return Text.Substring(start, length);
  }
}