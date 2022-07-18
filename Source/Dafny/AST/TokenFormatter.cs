using System;
using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Helpers;

public class HelperString {
  public static readonly System.Text.RegularExpressions.Regex NewlineRegex =
    new(@"(?<=\r?\n)\s*(?=(?<followedByChar>\S|$))");

  public static string Reindent(string input, string indentationBefore, string lastIndentation) {
    return NewlineRegex.Replace(input,
      (Match match) =>
        match.Groups["followedByChar"].Value.Length > 0 ? indentationBefore : lastIndentation);
  }
}

public class WhitespaceFormatter : TokenFormatter.ITokenIndentations {
  public Dictionary<IToken, int> TokenToMinIndentationBefore;
  public Dictionary<IToken, int> TokenToMinIndentationAfter;

  private WhitespaceFormatter(Dictionary<IToken, int> tokenToMinIndentationBefore, Dictionary<IToken, int> tokenToMinIndentationAfter) {
    TokenToMinIndentationBefore = tokenToMinIndentationBefore;
    TokenToMinIndentationAfter = tokenToMinIndentationAfter;
  }

  public static WhitespaceFormatter ForProgram(Program program) {
    Dictionary<IToken, int> tokenToMinIndentationBefore = new();
    Dictionary<IToken, int> tokenToMinIndentationAfter = new();

    foreach (var module in program.CompileModules) {

    }

    var formatter = new WhitespaceFormatter(tokenToMinIndentationBefore, tokenToMinIndentationAfter);
    return formatter;
  }

  class FormatterVisitor : BottomUpVisitor {

  }

  public void GetIndentation(IToken token, string currentIndentation, out string indentationBefore, out string lastIndentation,
    out string indentationAfter, out bool wasSet) {
    indentationBefore = currentIndentation;
    lastIndentation = currentIndentation;
    indentationAfter = currentIndentation;
    wasSet = false;
    if (TokenToMinIndentationBefore.TryGetValue(token, out var preIndentation)) {
      indentationBefore = new string(' ', preIndentation);
      lastIndentation = lastIndentation;
      indentationAfter = indentationBefore;
      wasSet = true;
    }
    if (TokenToMinIndentationAfter.TryGetValue(token, out var postIndentation)) {
      lastIndentation = new string(' ', postIndentation);
      indentationAfter = lastIndentation;
      wasSet = true;
    }
  }
}

public class DummyTokenIndentation : TokenFormatter.ITokenIndentations {
  public void GetIndentation(IToken token, string currentIndentation, out string indentationBefore, out string lastIndentation, out string indentationAfter,
    out bool wasSet) {
    if (token.val == "}") {
      wasSet = true;
      var indentationBeforeCount = token.col + 1;
      indentationBefore = new string(' ', indentationBeforeCount);
      lastIndentation = new string(' ', Math.Max(indentationBeforeCount - 2, 0));
      indentationAfter = lastIndentation;
    } else {
      wasSet = false;
      indentationBefore = "";
      lastIndentation = "";
      indentationAfter = "";
    }
  }
}
