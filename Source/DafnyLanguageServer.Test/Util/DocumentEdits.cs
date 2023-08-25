using System.Collections.Generic;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DocumentEdits {
  public static string ApplyEdits(TextDocumentEdit textDocumentEdit, string text) {
    return ApplyEdits(textDocumentEdit.Edits, text);
  }

  public static string ApplyEdits(IEnumerable<TextEdit> edits, string text) {
    var inversedEdits = edits.ToList()
      .OrderByDescending(x => x.Range.Start.Line)
      .ThenByDescending(x => x.Range.Start.Character);
    var modifiedText = ToLines(text);
    foreach (var textEdit in inversedEdits) {
      modifiedText = ApplyEditLinewise(modifiedText, textEdit.Range, textEdit.NewText);
    }

    return string.Join("\n", modifiedText);
  }


  public static List<string> ToLines(string text) {
    return text.ReplaceLineEndings("\n").Split("\n").ToList();
  }

  public static string FromLines(List<string> lines) {
    return string.Join("\n", lines).ReplaceLineEndings("\n");
  }

  public static string ApplyEdit(List<string> lines, Range range, string newText) {
    return FromLines(ApplyEditLinewise(lines, range, newText));
  }

  public static List<string> ApplyEditLinewise(List<string> lines, Range range, string newText) {
    var lineStart = lines[range.Start.Line];
    var lineEnd = lines[range.End.Line];
    lines[range.Start.Line] = lineStart[..range.Start.Character] + newText + lineEnd[range.End.Character..];
    lines = lines.Take(range.Start.Line).Concat(lines.Skip(range.End.Line)).ToList();
    return lines;
  }
}
