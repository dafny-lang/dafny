using System;
using System.Collections.Generic;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Helpers;

public class HelperString {
  public static readonly Regex NewlineRegex =
    new(@"(?<=\r?\n)[ \t]*(?<commentType>/\*[\s\S]*\*\/|//|\r?\n|$)");

  public static string Reindent(string input, string indentationBefore, string lastIndentation) {
    var commentExtra = "";
    // Invariant: Relative indentation inside a multi-line comment should be unchanged

    return NewlineRegex.Replace(input,
      (Match match) => {
        var result = indentationBefore;
        var v = match.Groups["commentType"].Value;
        if (v.Length > 0) {
          if (v.StartsWith("/*")) {
            // We reindent everything 
            commentExtra = new string(' ', match.Groups["followedByChar"].Value.Length - 1);
            return indentationBefore;
          } else if (v.StartsWith("*") ||
                     v.StartsWith("//")) {
            return indentationBefore + commentExtra;
          } else if (v.StartsWith("\r") || v.StartsWith("\n")) {
            return indentationBefore;
          } else { // For multi-line comments without stars.
            return indentationBefore + commentExtra + " ";
          }
        } else {
          result = lastIndentation;
          return result;
        }
      }
    );
  }
}

public class WhitespaceFormatter : TokenFormatter.ITokenIndentations {
  public Dictionary<int, int> TokenToMinIndentationBefore;
  public Dictionary<int, int> TokenToMinIndentationAfter;

  private WhitespaceFormatter(Dictionary<int, int> tokenToMinIndentationBefore, Dictionary<int, int> tokenToMinIndentationAfter) {
    TokenToMinIndentationBefore = tokenToMinIndentationBefore;
    TokenToMinIndentationAfter = tokenToMinIndentationAfter;
  }

  public static WhitespaceFormatter ForProgram(Program program) {
    Dictionary<int, int> posToMinIndentationBefore = new();
    Dictionary<int, int> posToMinIndentationAfter = new();

    var indent = 0;

    void SetMemberIndentation(MemberDecl member) {
      posToMinIndentationBefore.TryAdd(member.BodyStartTok.pos, indent);
      indent += 2;
      posToMinIndentationAfter.TryAdd(member.BodyStartTok.pos, indent);
      posToMinIndentationBefore.TryAdd(member.BodyEndTok.pos, indent);
      indent -= 2;
      posToMinIndentationAfter.TryAdd(member.BodyEndTok.pos, indent);
    }
    void SetDeclIndentation(TopLevelDecl topLevelDecl) {
      if (topLevelDecl.StartToken.line > 0) {
        posToMinIndentationBefore.TryAdd(topLevelDecl.BodyStartTok.pos, indent);
        indent += 2;
        posToMinIndentationAfter.TryAdd(topLevelDecl.BodyStartTok.pos, indent);
        if (topLevelDecl is LiteralModuleDecl moduleDecl) {
          foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
            SetDeclIndentation(decl2);
          }
        } else if (topLevelDecl is TopLevelDeclWithMembers declWithMembers) {
          foreach (var members in declWithMembers.Members) {
            SetMemberIndentation(members);
          }
        }
        posToMinIndentationBefore.TryAdd(topLevelDecl.BodyEndTok.pos, indent);
        indent -= 2;
        posToMinIndentationAfter.TryAdd(topLevelDecl.BodyEndTok.pos, indent);
      }
    }
    foreach (var decl in program.DefaultModuleDef.TopLevelDecls) {
      SetDeclIndentation(decl);
    }

    var formatter = new WhitespaceFormatter(posToMinIndentationBefore, posToMinIndentationAfter);
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
    if (TokenToMinIndentationBefore.TryGetValue(token.pos, out var preIndentation)) {
      indentationBefore = new string(' ', preIndentation);
      lastIndentation = lastIndentation;
      indentationAfter = indentationBefore;
      wasSet = true;
    }
    if (TokenToMinIndentationAfter.TryGetValue(token.pos, out var postIndentation)) {
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
