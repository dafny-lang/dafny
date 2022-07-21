using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Helpers;

public class HelperString {
  // If we ever decide that blank lines shouldn't have spaces, we can set this to true. 
  public const bool BlankNewlinesWithoutSpaces = false;

  public static readonly Regex NewlineRegex =
    new(@"(?<=\r?\n)(?<currentIndent>[ \t]*)(?<commentType>/\*[\s\S]*\*\/|//|\r?\n|$)");

  public static string Reindent(string input, string indentationBefore, string lastIndentation) {
    var commentExtra = "";
    // Invariant: Relative indentation inside a multi-line comment should be unchanged

    return NewlineRegex.Replace(input,
      match => {
        var commentType = match.Groups["commentType"].Value;
        if (commentType.Length > 0) {
          if (commentType.StartsWith("/*")) {
            var doubleStar = commentType.StartsWith("/**");
            var originalComment = match.Groups["commentType"].Value;
            var currentIndentation = match.Groups["currentIndent"].Value;
            var result = new Regex($@"(?<=\r?\n){currentIndentation}(?<star>\s*\*)?").Replace(
              originalComment, match1 => {
                if (match1.Groups["star"].Success) {
                  if (doubleStar) {
                    return indentationBefore + "  *";
                  } else {
                    return indentationBefore + " *";
                  }
                } else {
                  return indentationBefore + (match1.Groups["star"].Success ? match1.Groups["star"].Value : "");
                }
              });
            return indentationBefore + result;
          }

          if (commentType.StartsWith("//")) {
            return indentationBefore + match.Groups["commentType"].Value;
          }
          if (commentType.StartsWith("\r") || commentType.StartsWith("\n")) {
            return (BlankNewlinesWithoutSpaces ? "" : indentationBefore) + match.Groups["commentType"].Value;
          }
        }
        // Last line
        return lastIndentation;
      }
    );
  }
}

public class IndentationFormatter : TokenFormatter.ITokenIndentations {

  public Dictionary<int, int> TokenToIndentBefore;
  public Dictionary<int, int> TokenToIndentLineBefore;
  public Dictionary<int, int> TokenToIndentAfter;

  private IndentationFormatter(
    Dictionary<int, int> tokenToIndentBefore,
    Dictionary<int, int> tokenToIndentLineBefore,
    Dictionary<int, int> tokenToIndentAfter) {
    TokenToIndentBefore = tokenToIndentBefore;
    TokenToIndentLineBefore = tokenToIndentLineBefore;
    TokenToIndentAfter = tokenToIndentAfter;
  }

  public static IndentationFormatter ForProgram(Program program) {
    Dictionary<int, int> posToindentLinesBefore = new();
    Dictionary<int, int> posToIndentSameLineBefore = new();
    Dictionary<int, int> posToIndentAfter = new();

    var indent = 0;

    // Get the precise column this token will be at after reformatting.
    // Requires all tokens before to have been formatted.
    int GetTokenCol(IToken token) {
      var previousTrivia = token.Prev != null ? token.Prev.TrailingTrivia : "";
      previousTrivia += token.LeadingTrivia;
      var lastNL = previousTrivia.LastIndexOf('\n');
      var lastCR = previousTrivia.LastIndexOf('\r');
      if (lastNL >= 0 || lastCR >= 0) {
        // If the leading trivia contains an inline comment after the last newline, it can change the position.
        var lastCharacterAfterNewline = Math.Max(lastNL, lastCR) + 1;
        var lastTrivia = previousTrivia.Substring(lastCharacterAfterNewline);
        if (lastTrivia.IndexOf("*/", StringComparison.Ordinal) >= 0) {
          return lastTrivia.Length + 1;
        }
        if (posToIndentSameLineBefore.TryGetValue(token.pos, out var indentation)) {
          return indentation + 1;
        }
        return indent + 1;
      }
      // No newline, so no re-indentation.
      if (token.Prev != null) {
        return GetTokenCol(token.Prev) + token.Prev.val.Length + previousTrivia.Length;
      }

      return token.col;
    }

    void SetBeforeAfter(IToken token, int before, int sameLineBefore, int after) {
      if (before >= 0) {
        posToindentLinesBefore[token.pos] = before;
      }

      if (sameLineBefore >= 0) {
        posToIndentSameLineBefore[token.pos] = sameLineBefore;
      }

      if (after >= 0) {
        posToIndentAfter[token.pos] = after;
      }
    }

    void SetMemberIndentation(MemberDecl member) {
      if (member is Method method) {
        // Owned tokens ("method" can also be "lemma" or "ghost method"
        // "<FIRST>">2 "[">2 "]"<2 "<">Align <$","*>$ ">">Align "(">Align <$",">$ ")">Align
        // 
        // method Id [ nat ] < , > ( , , ) returns ( , , )
        //
        // method Id [ nat ] < , >
        //   (x: int, // indentation after ( = indentation before + 1 + length of space if no newline
        //    y: int  // indentation is copied from the first (
        // , , ) // indentation after ) is the indentation before (
        // returns ( , , )
        // method {:fuel xxxx} Id<VeryLongTypeParameters>(
        //     x: int,
        //     y: int)
        var initialIndent = indent;
        SetBeforeAfter(method.StartToken, indent, indent, indent + 2);
        indent += 2;
        var firstParenthesis = true;
        var extraIndent = 0;
        var commaIndent = 0;
        foreach (var token in method.OwnedTokens) {
          if (token.val is "<" or "[" or "(") {
            if (token.TrailingTrivia.Contains('\r') || token.TrailingTrivia.Contains('\n')) {
              extraIndent = 2;
              commaIndent = indent;
            } else { // Align capabilities
              var c = 0;
              while (c < token.TrailingTrivia.Length && token.TrailingTrivia[c] == ' ') {
                c++;
              }
              extraIndent = GetTokenCol(token) + c - indent;
              commaIndent = GetTokenCol(token) - 1;
            }
            SetBeforeAfter(token, indent, indent, indent + extraIndent);
            indent += extraIndent;
            if (token.val is "<") {
              // TODO: Type parameters here
            } else if (token.val is "(") {
              // TODO: Formals here
            }
          }
          if (token.val is ",") {
            SetBeforeAfter(token, indent, commaIndent, indent);
          }
          if (token.val is ">" or "]" or ")") {
            indent -= extraIndent;
            SetBeforeAfter(token, indent + extraIndent, indent, indent);
          }
        }
        // TODO: Frame expressions here

        indent = initialIndent;
      }

      if (member.BodyStartTok.line > 0) {
        SetBeforeAfter(member.BodyStartTok, indent + 2, indent, indent + 2);
      }
      // TODO: Body here

      indent += 2;
      if (member is Method) {

      }

      indent -= 2;
      SetBeforeAfter(member.BodyEndTok, indent + 2, indent, indent);
      posToIndentAfter[member.EndToken.pos] = indent;
    }
    void SetDeclIndentation(TopLevelDecl topLevelDecl) {
      var initIndent = indent;
      if (topLevelDecl.StartToken.line > 0) {
        SetBeforeAfter(topLevelDecl.BodyStartTok, indent, indent, indent + 2);
        indent += 2;
      }
      if (topLevelDecl is LiteralModuleDecl moduleDecl) {
        foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
          SetDeclIndentation(decl2);
        }
      } else if (topLevelDecl is TopLevelDeclWithMembers declWithMembers) {
        foreach (var members in declWithMembers.Members) {
          SetMemberIndentation(members);
        }
      }
      if (topLevelDecl.StartToken.line > 0) {
        SetBeforeAfter(topLevelDecl.EndToken, indent, initIndent, initIndent);
        indent = initIndent;
      }
    }
    foreach (var decl in program.DefaultModuleDef.TopLevelDecls) {
      SetDeclIndentation(decl);
    }

    var formatter = new IndentationFormatter(posToindentLinesBefore, posToIndentSameLineBefore, posToIndentAfter);
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
    if (TokenToIndentBefore.TryGetValue(token.pos, out var preIndentation)) {
      indentationBefore = new string(' ', preIndentation);
      lastIndentation = lastIndentation;
      indentationAfter = indentationBefore;
      wasSet = true;
    }
    if (TokenToIndentLineBefore.TryGetValue(token.pos, out var sameLineIndentation)) {
      lastIndentation = new string(' ', sameLineIndentation);
      indentationAfter = lastIndentation;
      wasSet = true;
    }
    if (TokenToIndentAfter.TryGetValue(token.pos, out var postIndentation)) {
      indentationAfter = new string(' ', postIndentation);
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
