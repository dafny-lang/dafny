using System.Collections.Generic;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DocumentEdits {
  public static List<string> ApplyEdits(TextDocumentEdit textDocumentEdit, string output) {
    var inversedEdits = textDocumentEdit.Edits.ToList()
      .OrderByDescending(x => x.Range.Start.Line)
      .ThenByDescending(x => x.Range.Start.Character);
    var modifiedOutput = ToLines(output);
    foreach (var textEdit in inversedEdits) {
      modifiedOutput = ApplySingleEdit(modifiedOutput, textEdit.Range, textEdit.NewText);
    }

    return modifiedOutput;
  }

  public static List<string> ToLines(string output) {
    return output.ReplaceLineEndings("\n").Split("\n").ToList();
  }

  public static List<string> ApplySingleEdit(List<string> modifiedOutput, Range range, string newText) {
    var lineStart = modifiedOutput[range.Start.Line];
    var lineEnd = modifiedOutput[range.End.Line];
    modifiedOutput[range.Start.Line] =
      lineStart.Substring(0, range.Start.Character) + newText +
      lineEnd.Substring(range.End.Character);
    modifiedOutput = modifiedOutput.Take(range.Start.Line).Concat(
      modifiedOutput.Skip(range.End.Line)
    ).ToList();
    return modifiedOutput;
  }
}
