﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny.Triggers;

namespace Microsoft.Dafny.Helpers;

public class HelperString {
  // If we ever decide that blank lines shouldn't have spaces, we can set this to true. 
  public static bool BlankNewlinesWithoutSpaces = false;

  // If we remove whitespace (tabs or space) at the end of lines. 
  public static bool RemoveTrailingWhitespace = true;

  public static readonly Regex NewlineRegex =
    new(@"(?<=\r?\n)(?<currentIndent>[ \t]*)(?<commentType>/\*[\s\S]*\*\/|//|\r?\n|$)|(?<=\S|^)(?<trailingWhitespace>[ \t]+)(?=\r?\n)");

  public static string Reindent(string input, string indentationBefore, string lastIndentation) {
    var commentExtra = "";
    // Invariant: Relative indentation inside a multi-line comment should be unchanged

    return NewlineRegex.Replace(input,
      match => {
        if (match.Groups["trailingWhitespace"].Success) {
          return RemoveTrailingWhitespace ? "" : match.Groups["trailingWhitespace"].Value;
        } else {
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
      }
    );
  }
}

public class IndentationFormatter : TokenFormatter.ITokenIndentations {

  public Dictionary<int, int> PosToIndentBefore;
  public Dictionary<int, int> PosToIndentLineBefore;
  public Dictionary<int, int> PosToIndentAfter;

  private IndentationFormatter(
    Dictionary<int, int> posToIndentBefore,
    Dictionary<int, int> posToIndentLineBefore,
    Dictionary<int, int> posToIndentAfter) {
    PosToIndentBefore = posToIndentBefore;
    PosToIndentLineBefore = posToIndentLineBefore;
    PosToIndentAfter = posToIndentAfter;
  }


  // Given a token, finds the indentation that was expected before it.
  // Used for frame expressions to initially copy the indentation of "reads", "requires", etc.
  private int GetIndentAfter(IToken token) {
    if (token == null) {
      return 0;
    }
    if (PosToIndentAfter.TryGetValue(token.pos, out var indentation)) {
      return indentation;
    }
    return GetIndentAfter(token.Prev);
  }


  // Get the precise column this token will be at after reformatting.
  // Requires all tokens before to have been formatted.
  private int GetTokenCol(IToken token, int indent) {
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
      if (PosToIndentLineBefore.TryGetValue(token.pos, out var indentation)) {
        return indentation + 1;
      }
      if (token.Prev != null &&
          PosToIndentAfter.TryGetValue(token.Prev.pos, out var indentation2)) {
        return indentation2 + 1;
      }
      return indent + 1;
    }
    // No newline, so no re-indentation.
    if (token.Prev != null) {
      return GetTokenCol(token.Prev, indent) + token.Prev.val.Length + previousTrivia.Length;
    }

    return token.col;
  }

  private void SetBeforeAfter(IToken token, int before, int sameLineBefore, int after) {
    if (before >= 0) {
      PosToIndentLineBefore[token.pos] = before;
    }

    if (sameLineBefore >= 0) {
      PosToIndentLineBefore[token.pos] = sameLineBefore;
    }

    if (after >= 0) {
      PosToIndentAfter[token.pos] = after;
    }
  }

  void MarkMethodLikeIndent(IToken startToken, List<IToken> ownedTokens, int indent) {
    SetBeforeAfter(startToken, indent, indent, indent + 2);
    indent += 2;
    var specIndent = indent;
    var firstParenthesis = true;
    var extraIndent = 0;
    var commaIndent = 0;
    foreach (var token in ownedTokens) {
      if (token.val is "<" or "[" or "(" or "{") {
        if (token.TrailingTrivia.Contains('\r') || token.TrailingTrivia.Contains('\n')) {
          extraIndent = 2;
          commaIndent = indent;
        } else {
          // Align capabilities
          var c = 0;
          while (c < token.TrailingTrivia.Length && token.TrailingTrivia[c] == ' ') {
            c++;
          }

          extraIndent = GetTokenCol(token, indent) + c - indent;
          commaIndent = GetTokenCol(token, indent) - 1;
        }

        SetBeforeAfter(token, indent, indent, indent + extraIndent);
        indent += extraIndent;
      }
      if (token.val is ",") {
        SetBeforeAfter(token, indent, commaIndent, indent);
      }
      if (token.val is ">" or "]" or ")" or "}") {
        indent -= extraIndent;
        SetBeforeAfter(token, indent + extraIndent, indent, indent);
      }

      if (token.val is "reads" or "modifies" or "decreases" or "requires" or "ensures" or "invariant") {
        indent = specIndent;
        SetBeforeAfter(token, indent, indent, indent + 2);
        indent += 2;
        commaIndent = indent;
      }
    }
  }

  void SetTypeIndentation(IToken token, Type type) {
    var indent = GetIndentAfter(token.Prev);
    // TODO
  }

  void SetAttributeIndentation(Attributes attributes) {
    // TODO
  }

  void SetAttributedExpressionIndentation(AttributedExpression attrExpression) {
    SetAttributeIndentation(attrExpression.Attributes);
    SetExpressionIndentation(attrExpression.E);
  }

  void SetFrameExpressionIndentation(FrameExpression frameExpression) {
    SetExpressionIndentation(frameExpression.E);
  }

  void SetExpressionIndentation(Expression expression) {
    var visitor = new FormatterVisitor();
    visitor.Visit(expression);
  }

  void SetStatementIndentation(Statement statement) {
    // TODO
  }

  void SetMemberIndentation(MemberDecl member, int indent) {
    var savedIndent = indent;
    MarkMethodLikeIndent(member.StartToken, member.OwnedTokens, indent);
    if (member.BodyStartTok.line > 0) {
      SetBeforeAfter(member.BodyStartTok, indent + 2, indent, indent + 2);
    }

    if (member is Method method) {
      foreach (var formal in method.Ins) {
        SetTypeIndentation(formal.tok, formal.SyntacticType);
      }
      foreach (var formal in method.Outs) {
        SetTypeIndentation(formal.tok, formal.SyntacticType);
      }
      foreach (var req in method.Req) {
        SetAttributedExpressionIndentation(req);
      }
      foreach (var mod in method.Mod.Expressions) {
        SetFrameExpressionIndentation(mod);
      }
      foreach (var ens in method.Ens) {
        SetAttributedExpressionIndentation(ens);
      }
      foreach (var dec in method.Decreases.Expressions) {
        SetExpressionIndentation(dec);
      }
      SetStatementIndentation(method.Body);
    }
    if (member is Function function) {
      SetExpressionIndentation(function.Body);
    }

    // TODO: Body here
    indent = savedIndent;
    indent += 2;
    if (member is Method) {

    }
    indent -= 2;
    if (member.BodyEndTok.line > 0) {
      SetBeforeAfter(member.BodyEndTok, indent + 2, indent, indent);
    }

    PosToIndentAfter[member.EndToken.pos] = indent;
  }

  private void SetDeclIndentation(TopLevelDecl topLevelDecl, int indent) {
    var initIndent = indent;
    if (topLevelDecl.StartToken.line > 0) {
      SetBeforeAfter(topLevelDecl.BodyStartTok, indent, indent, indent + 2);
      indent += 2;
    }
    if (topLevelDecl is LiteralModuleDecl moduleDecl) {
      foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
        SetDeclIndentation(decl2, indent);
      }
    } else if (topLevelDecl is TopLevelDeclWithMembers declWithMembers) {
      foreach (var members in declWithMembers.Members) {
        SetMemberIndentation(members, indent);
      }
    }
    if (topLevelDecl.StartToken.line > 0) {
      SetBeforeAfter(topLevelDecl.EndToken, indent, initIndent, initIndent);
      indent = initIndent;
    }
  }
  public static IndentationFormatter ForProgram(Program program) {
    var indentationFormatter = new IndentationFormatter(
      new(),
      new(),
      new());

    foreach (var decl in program.DefaultModuleDef.TopLevelDecls) {
      indentationFormatter.SetDeclIndentation(decl, 0);
    }

    return indentationFormatter;
  }

  class FormatterVisitor : BottomUpVisitor {

  }

  public void GetIndentation(IToken token, string currentIndentation, out string indentationBefore, out string lastIndentation,
    out string indentationAfter, out bool wasSet) {
    indentationBefore = currentIndentation;
    lastIndentation = currentIndentation;
    indentationAfter = currentIndentation;
    wasSet = false;
    if (PosToIndentBefore.TryGetValue(token.pos, out var preIndentation)) {
      indentationBefore = new string(' ', preIndentation);
      lastIndentation = lastIndentation;
      indentationAfter = indentationBefore;
      wasSet = true;
    }
    if (PosToIndentLineBefore.TryGetValue(token.pos, out var sameLineIndentation)) {
      lastIndentation = new string(' ', sameLineIndentation);
      indentationAfter = lastIndentation;
      wasSet = true;
    }
    if (PosToIndentAfter.TryGetValue(token.pos, out var postIndentation)) {
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
