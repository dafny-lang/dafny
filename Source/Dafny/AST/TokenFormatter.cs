using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Serialization;
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

  private int GetIndentBefore(IToken token) {
    if (PosToIndentLineBefore.TryGetValue(token.pos, out var indentation)) {
      return indentation;
    }
    if (PosToIndentBefore.TryGetValue(token.pos, out var indentation2)) {
      return indentation2;
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

  // 'before' is the hypothetical indentation of a comment before that token, and of the previous token if it does not have a set indentation
  // 'sameLineBefore' is the hypothetical indentation of this token if it was on its own line
  // 'after' is the hypothetical indentation of a comment after that token, and of the next token if it does not have a set indentation
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

  void MarkMethodLikeIndent(IToken startToken, IEnumerable<IToken> ownedTokens, int indent) {
    var initIndent = indent;
    if (startToken.val != "{") {
      SetBeforeAfter(startToken, -1, indent, indent + 2);
      indent += 2;
    } else {
      if (PosToIndentLineBefore.TryGetValue(startToken.pos, out var lineIndent)) {
        indent = lineIndent + 2;
      }
    }
    var firstIndent = indent;
    var extraIndent = 0;
    var commaIndent = 0;
    foreach (var token in ownedTokens) {
      if (token.val is "{") {
        SetBeforeAfter(token, initIndent + 2, initIndent, initIndent + 2);
        indent += 2;
      }
      if (token.val is "<" or "[" or "(") {
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
      if (token.val is ">" or "]" or ")") {
        indent -= extraIndent;
        SetBeforeAfter(token, indent + extraIndent, indent, indent);
      }
      if (token.val is "}" && !PosToIndentLineBefore.ContainsKey(token.pos)) {
        indent -= 2;
        SetBeforeAfter(token, indent + 2, indent, indent);
      }
      if (token.val is "reads" or "modifies" or "decreases" or "requires" or "ensures" or "invariant") {
        indent = firstIndent;
        SetBeforeAfter(token, indent, indent, indent + 2);
        indent += 2;
        commaIndent = indent;
      }
    }
  }

  void SetTypeIndentation(IToken token, Type type) {
    var indent = GetIndentBefore(token);
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
    var visitor = new FormatterVisitor(this);
    visitor.Visit(expression, GetIndentBefore(expression.StartToken));
  }

  void SetStatementIndentation(Statement statement) {
    var visitor = new FormatterVisitor(this);
    visitor.Visit(statement, GetIndentBefore(statement.Tok));
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

      if (method.Body != null) {
        SetStatementIndentation(method.Body);
      }
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

  class FormatterVisitor : TopDownVisitor<int> {
    private IndentationFormatter formatter;
    private int binOpIndent = -1;
    private int binOpArgIndent = -1;

    public FormatterVisitor(IndentationFormatter formatter) {
      this.formatter = formatter;
      this.preResolve = true;
    }

    protected override bool VisitOneStmt(Statement stmt, ref int unusedIndent) {
      /*if (stmt.OwnedTokens.Count > 0) {
        var firstToken = stmt.OwnedTokens[0];
        var indent = formatter.GetTokenCol(firstToken, formatter.GetIndentBefore(firstToken)) - 1;
        
      }
      return true;*/
      var firstToken = stmt.Tok;
      var indent = formatter.GetIndentBefore(firstToken);
      if (stmt is IfStmt ifStmt) {
        if (ifStmt.OwnedTokens.Count > 0) {
          formatter.SetOpeningIndentedRegion(ifStmt.OwnedTokens[0], indent);
        }
        formatter.SetDelimiterIndentedRegions(ifStmt.Thn.Tok, indent);
        formatter.SetClosingIndentedRegion(ifStmt.Thn.EndTok, indent);
        if (ifStmt.OwnedTokens.Count > 1) { // "else"
          formatter.SetKeywordWithoutSurroundingIndentation(ifStmt.OwnedTokens[1], indent);
        }
        if (ifStmt.Els != null) {
          formatter.SetOpeningIndentedRegion(ifStmt.Els.Tok, indent);
          formatter.SetClosingIndentedRegion(ifStmt.Els.EndTok, indent);
        }
      } else if (stmt is ForallStmt forallStmt) {
        if (forallStmt.OwnedTokens.Count > 0) {
          formatter.SetOpeningIndentedRegion(forallStmt.OwnedTokens[0], indent);
        }
        for (var i = 1; i < forallStmt.OwnedTokens.Count; i++) {
          formatter.SetSpecification(forallStmt.OwnedTokens[i], indent);
        }
        formatter.SetDelimiterIndentedRegions(forallStmt.Body.Tok, indent);
        formatter.SetClosingIndentedRegion(forallStmt.Body.EndTok, indent);
      } else if (stmt is WhileStmt whileStmt) {
        if (whileStmt.OwnedTokens.Count > 0) {
          formatter.SetOpeningIndentedRegion(whileStmt.OwnedTokens[0], indent);
        }
        for (var i = 1; i < whileStmt.OwnedTokens.Count; i++) {
          formatter.SetSpecification(whileStmt.OwnedTokens[i], indent);
        }
        formatter.SetDelimiterIndentedRegions(whileStmt.Body.Tok, indent);
        formatter.SetClosingIndentedRegion(whileStmt.Body.EndTok, indent);
      } else if (stmt is ForLoopStmt forLoopStmt) {
        if (forLoopStmt.OwnedTokens.Count > 0) {
          formatter.SetOpeningIndentedRegion(forLoopStmt.OwnedTokens[0], indent);
        }
        for (var i = 1; i < forLoopStmt.OwnedTokens.Count; i++) {
          formatter.SetSpecification(forLoopStmt.OwnedTokens[i], indent);
        }
        formatter.SetDelimiterIndentedRegions(forLoopStmt.Body.Tok, indent);
        formatter.SetClosingIndentedRegion(forLoopStmt.Body.EndTok, indent);
      } else {
        formatter.MarkMethodLikeIndent(stmt.Tok, stmt.OwnedTokens, indent);
        formatter.SetBeforeAfter(stmt.EndTok, -1, -1, indent);
      }

      return true;
    }

    protected override bool VisitOneExpr(Expression expr, ref int unusedIndent) {
      if (expr is BinaryExpr binaryExpr) {
        if (binaryExpr.Op is BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or) { // Alignment required.
          if (binaryExpr.OwnedTokens.Count == 2) {
            var firstToken = binaryExpr.OwnedTokens[0];
            var secondToken = binaryExpr.OwnedTokens[1];
            var newIndent = formatter.GetTokenCol(firstToken, formatter.GetIndentBefore(firstToken)) - 1;
            var c = 0;
            while (c < firstToken.TrailingTrivia.Length && firstToken.TrailingTrivia[c] == ' ') {
              c++;
            }
            var conjunctExtraIndent = c + 2;
            binOpIndent = newIndent;
            binOpArgIndent = newIndent + conjunctExtraIndent;
            formatter.SetBeforeAfter(firstToken, binOpIndent, binOpIndent, binOpArgIndent);
            formatter.SetBeforeAfter(secondToken, binOpIndent, binOpIndent, binOpArgIndent);
          } else {
            if (binOpIndent > 0) {
              formatter.SetBeforeAfter(binaryExpr.OwnedTokens[0], binOpIndent, binOpIndent, binOpArgIndent);
            } else if (binaryExpr.OwnedTokens.Count > 0) {
              var startToken = binaryExpr.StartToken;
              var newIndent = formatter.GetTokenCol(startToken, formatter.GetIndentBefore(startToken)) - 1;
              formatter.SetBeforeAfter(binaryExpr.OwnedTokens[0], newIndent, newIndent, newIndent);
            }
          }
          if (binOpIndent > 0 && (binaryExpr.E0 is not BinaryExpr { Op: var op } || op != binaryExpr.Op)) {
            binOpIndent = -1;
            binOpArgIndent = -1;
          }
        }
      } else if (expr is QuantifierExpr) {

      } // TODO

      return true;
    }
  }

  private void SetOpeningIndentedRegion(IToken token, int indent) {
    SetBeforeAfter(token, indent, indent, indent + 2);
  }

  private void SetSpecification(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent + 2, indent + 4);
  }

  private void SetDelimiterIndentedRegions(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent, indent + 2);
  }


  private void SetClosingIndentedRegion(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent, indent);
  }
  private void SetKeywordWithoutSurroundingIndentation(IToken token, int indent) {
    SetBeforeAfter(token, indent, indent, indent);
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
