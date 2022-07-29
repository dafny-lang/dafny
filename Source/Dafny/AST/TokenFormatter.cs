using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Serialization;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny.Triggers;

namespace Microsoft.Dafny.Helpers;

public class HelperString {
  // If we ever decide that blank lines shouldn't have spaces, we can set this to true. 
  public static bool BlankNewlinesWithoutSpaces = false;

  // If we remove whitespace (tabs or space) at the end of lines. 
  public static bool RemoveTrailingWhitespace = true;

  public static readonly Regex NewlineRegex =
    new(@"(?<=\r?\n|\r(?!\n))(?<currentIndent>[ \t]*)(?<commentType>/\*[\s\S]*\*\/|//|\r?\n|\r(?!\n)|$)|(?<=\S|^)(?<trailingWhitespace>[ \t]+)(?=\r?\n|\r(?!\n))");

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
              var result = new Regex($@"(?<=\r?\n|\r(?!\n)){currentIndentation}(?<star>\s*\*)?").Replace(
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
      PosToIndentBefore[token.pos] = before;
    }

    if (sameLineBefore >= 0) {
      PosToIndentLineBefore[token.pos] = sameLineBefore;
    }

    if (after >= 0) {
      PosToIndentAfter[token.pos] = after;
    }
  }

  void MarkMethodLikeIndent(IToken startToken, IEnumerable<IToken> ownedTokens, int indent) {
    var indent2 = indent + 2;
    if (startToken.val != "{") {
      SetBeforeAfter(startToken, -1, indent, indent2);
    }
    var extraIndent = 0;
    var commaIndent = 0;
    foreach (var token in ownedTokens) {
      if (token.val is "{") {
        SetDelimiterIndentedRegions(token, indent);
      }
      if (token.val is "<" or "[" or "(") {
        if (IsFollowedByNewline(token)) {
          extraIndent = 2;
          commaIndent = indent2;
        } else {
          // Align capabilities
          var rightIndent = GetRightAlignIndentAfter(token, indent2);
          commaIndent = GetRightAlignIndentDelimiter(token, indent2);
          extraIndent = rightIndent - indent2;
        }

        SetBeforeAfter(token, indent2, indent2, indent2 + extraIndent);
      }
      if (token.val is ",") {
        SetBeforeAfter(token, indent2 + extraIndent, commaIndent, indent2 + extraIndent);
      }
      if (token.val is ">" or "]" or ")") {
        SetBeforeAfter(token, indent2 + extraIndent, indent2, indent2);
      }
      if (token.val is "}" && !PosToIndentLineBefore.ContainsKey(token.pos)) {
        SetClosingIndentedRegion(token, indent);
      }
      if (token.val is "reads" or "modifies" or "decreases" or "requires" or "ensures" or "invariant") {
        SetOpeningIndentedRegion(token, indent2);
        commaIndent = indent2;
      }
    }
  }

  private static int GetTrailingSpace(IToken token) {
    var c = 0;
    while (c < token.TrailingTrivia.Length && token.TrailingTrivia[c] == ' ') {
      c++;
    }

    return c;
  }

  // Given a token such as `var ` immediately followed by another token
  // returns the indent so that everything after it is aligned with the first token.
  private int GetRightAlignIndentAfter(IToken token, int indentFallback) {
    var trailingSpace = GetTrailingSpace(token);
    return GetTokenCol(token, indentFallback) - 1 + token.val.Length + trailingSpace;
  }

  private int GetRightAlignIndentDelimiter(IToken token, int indentFallback) {
    return GetTokenCol(token, indentFallback) - 1 + token.val.Length - 1;
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
    if (expression != null) {
      var visitor = new FormatterVisitor(this);
      visitor.Visit(expression, GetIndentBefore(expression.StartToken));
    }
  }

  void SetStatementIndentation(Statement statement) {
    var visitor = new FormatterVisitor(this);
    visitor.Visit(statement, GetIndentBefore(statement.Tok));
  }

  void SetMemberIndentation(MemberDecl member, int indent) {
    var savedIndent = indent;
    MarkMethodLikeIndent(member.StartToken, member.OwnedTokens, indent);
    if (member.BodyStartTok.line > 0) {
      SetDelimiterIndentedRegions(member.BodyStartTok, indent);
    }

    switch (member) {
      case Field field:
        SetOpeningIndentedRegion(field.StartToken, indent);
        SetClosingIndentedRegion(field.EndToken, indent);
        switch (field) {
          case ConstantField constantField:
            var ownedTokens = constantField.OwnedTokens;
            var commaIndent = indent + 2;
            var rightIndent = indent + 2;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case ":=": {
                    if (IsFollowedByNewline(token)) {
                      SetDelimiterInsideIndentedRegions(token, indent);
                    } else {
                      SetBeforeAfter(token, indent + 2, indent + 2, -1);
                      rightIndent = GetRightAlignIndentAfter(token, indent);
                      commaIndent = GetRightAlignIndentDelimiter(token, indent);
                      SetBeforeAfter(token, -1, -1, rightIndent);
                    }
                    break;
                  }
                case ",": {
                    SetBeforeAfter(token, rightIndent, commaIndent, rightIndent);
                    break;
                  }
                case ";": {
                    break;
                  }
              }
            }
            if (constantField.Rhs is { } constantFieldRhs) {
              SetExpressionIndentation(constantFieldRhs);
            }

            break;
        }
        break;
      case Method method: {
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

          break;
        }
      case Function function: {
          foreach (var formal in function.Formals) {
            SetTypeIndentation(formal.tok, formal.SyntacticType);
          }
          if (function.Result is { } outFormal) {
            SetTypeIndentation(outFormal.tok, outFormal.SyntacticType);
          }
          foreach (var req in function.Req) {
            SetAttributedExpressionIndentation(req);
          }
          foreach (var frame in function.Reads) {
            SetFrameExpressionIndentation(frame);
          }
          foreach (var ens in function.Ens) {
            SetAttributedExpressionIndentation(ens);
          }
          foreach (var dec in function.Decreases.Expressions) {
            SetExpressionIndentation(dec);
          }
          if (function.ByMethodBody is { } byMethodBody) {
            SetDelimiterIndentedRegions(byMethodBody.StartToken, indent);
            SetClosingIndentedRegion(byMethodBody.EndTok, indent);
            SetStatementIndentation(byMethodBody);
          }
          SetExpressionIndentation(function.Body);
          break;
        }
    }

    // TODO: Body here
    indent = savedIndent;
    if (member.BodyEndTok.line > 0) {
      SetBeforeAfter(member.BodyEndTok, indent + 2, indent, indent);
    }

    PosToIndentAfter[member.EndToken.pos] = indent;
  }

  private void SetDeclIndentation(TopLevelDecl topLevelDecl, int indent) {
    var indent2 = indent + 2;
    if (topLevelDecl.StartToken.line > 0) {
      SetOpeningIndentedRegion(topLevelDecl.BodyStartTok, indent);
    }
    if (topLevelDecl is LiteralModuleDecl moduleDecl) {
      foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
        SetDeclIndentation(decl2, indent2);
      }
    } else if (topLevelDecl is TopLevelDeclWithMembers declWithMembers) {
      // TODO: Classes, Traits
      if (declWithMembers is DatatypeDecl datatypeDecl) {
        SetClosingIndentedRegion(datatypeDecl.EndToken, indent);
        var verticalBarIndent = indent2;
        var rightOfVerticalBarIndent = indent2;
        var commaIndent = indent2;
        var rightIndent = indent2;
        foreach (var token in datatypeDecl.OwnedTokens) {
          switch (token.val) {
            case "|": {
                SetBeforeAfter(token, rightOfVerticalBarIndent, verticalBarIndent, rightOfVerticalBarIndent);
                break;
              }
            case "(": {
                break;
              }
            case ")": {
                break;
              }
            case "=": {
                if (IsFollowedByNewline(token)) {
                  SetDelimiterInsideIndentedRegions(token, indent2);
                } else {
                  SetBeforeAfter(token, indent2, indent2, -1);
                  rightOfVerticalBarIndent = GetRightAlignIndentAfter(token, indent);
                  verticalBarIndent = GetRightAlignIndentDelimiter(token, indent);
                  SetBeforeAfter(token, -1, -1, rightOfVerticalBarIndent);
                }

                break;
              }
            case ",": {
                SetBeforeAfter(token, rightIndent, commaIndent, rightIndent);
                break;
              }
            case ";": {
                break;
              }
          }
        }
      }
      foreach (var members in declWithMembers.Members) {
        SetMemberIndentation(members, indent2);
      }
    }
    if (topLevelDecl.StartToken.line > 0 && topLevelDecl.EndToken.val == "}") {
      SetBeforeAfter(topLevelDecl.EndToken, indent2, indent, indent);
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

  public static bool IsFollowedByNewline(IToken token) {
    return token.TrailingTrivia.Contains('\n') || token.TrailingTrivia.Contains('\r');
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
      switch (stmt) {
        case BlockStmt blockStmt: {
            foreach (var token in blockStmt.OwnedTokens) {
              if (!formatter.PosToIndentBefore.ContainsKey(token.pos)) {
                if (token.val == "{") {
                  formatter.SetDelimiterIndentedRegions(token, indent);
                } else if (token.val == "}") {
                  formatter.SetClosingIndentedRegion(token, indent);
                }
              }
            }

            break;
          }
        case IfStmt ifStmt: {
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

            break;
          }
        case ForallStmt forallStmt:
          FormatLikeLoop(forallStmt.OwnedTokens, forallStmt.Body, indent);
          break;
        case WhileStmt whileStmt:
          FormatLikeLoop(whileStmt.OwnedTokens, whileStmt.Body, indent);
          break;
        case ForLoopStmt forLoopStmt: {
            var ownedTokens = forLoopStmt.OwnedTokens;
            if (ownedTokens.Count > 0) {
              formatter.SetOpeningIndentedRegion(ownedTokens[0], indent);
            }

            var specification = false;
            for (var i = 1; i < ownedTokens.Count; i++) {
              if (specification) {
                formatter.SetOpeningIndentedRegion(ownedTokens[i], indent + 2);
              }

              if (ownedTokens[i].val == "to") {
                specification = true;
              }
            }
            formatter.SetDelimiterIndentedRegions(forLoopStmt.Body.Tok, indent);
            formatter.SetClosingIndentedRegion(forLoopStmt.Body.EndTok, indent);
            break;
          }
        case VarDeclStmt varDeclStmt: {
            var ownedTokens = varDeclStmt.OwnedTokens;
            ApplyVarAssignFormatting(indent, ownedTokens);

            break;
          }
        case AssignSuchThatStmt:
        case AssignOrReturnStmt:
        case UpdateStmt: {
            var ownedTokens = stmt.OwnedTokens;
            var authorizeFlattening = false;
            var commaIndent = indent + 2;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case ",":
                  if (authorizeFlattening) {
                    formatter.SetDelimiterInsideIndentedRegions(token, indent);
                  } else {
                    formatter.SetDelimiterIndentedRegions(token, commaIndent);
                  }
                  break;
                case ":|":
                case ":-":
                case ":=":
                  if (IsFollowedByNewline(token)) {
                    formatter.SetDelimiterInsideIndentedRegions(token, indent);
                    authorizeFlattening = true;
                  } else {
                    formatter.SetBeforeAfter(token, indent + 2, indent + 2, -1);
                    var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
                    commaIndent = formatter.GetRightAlignIndentDelimiter(token, indent);
                    formatter.SetBeforeAfter(token, -1, -1, rightIndent);
                    authorizeFlattening = false;
                  }

                  break;
                case ";":
                  formatter.SetClosingIndentedRegionInside(token, indent);
                  break;
                  // Otherwise, these are identifiers, We don't need to specify their indentation.
              }
            }

            break;
          }
        case NestedMatchStmt: {
            var ownedTokens = stmt.OwnedTokens;
            ApplyMatchFormatting(indent, ownedTokens);
            break;
          }
        case RevealStmt:
        case PrintStmt: {
            var ownedTokens = stmt.OwnedTokens;
            var commaIndent = indent + 2;
            var innerIndent = indent + 2;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case "reveal":
                case "print":
                  if (IsFollowedByNewline(token)) {
                    formatter.SetDelimiterInsideIndentedRegions(token, indent);
                  } else {
                    formatter.SetBeforeAfter(token, indent, indent, -1);
                    innerIndent = formatter.GetRightAlignIndentAfter(token, indent);
                    commaIndent = formatter.GetRightAlignIndentDelimiter(token, indent);
                    formatter.SetBeforeAfter(token, -1, -1, innerIndent);
                  }
                  formatter.SetOpeningIndentedRegion(token, indent);
                  break;
                case ",":
                  formatter.SetBeforeAfter(token, innerIndent, commaIndent, innerIndent);
                  break;
                case ";":
                  formatter.SetClosingIndentedRegionInside(token, indent);
                  break;
              }
            }

            break;
          }
        case AssumeStmt:
        case ExpectStmt:
        case AssertStmt: {
            var ownedTokens = stmt.OwnedTokens;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case "assume":
                case "expect":
                case "assert":
                  formatter.SetOpeningIndentedRegion(token, indent);
                  break;
                case "}":
                case "by":
                  formatter.SetClosingIndentedRegion(token, indent);
                  break;
                case ";":
                  formatter.SetClosingIndentedRegionInside(token, indent);
                  break;
                case "{":
                  formatter.SetOpeningIndentedRegion(token, indent);
                  break;
              }
            }

            if (stmt is AssertStmt { Proof: { StartToken: { } startToken } } assertStmt) {
              formatter.SetOpeningIndentedRegion(startToken, indent);
            }
            break;
          }
        default:
          formatter.MarkMethodLikeIndent(stmt.Tok, stmt.OwnedTokens, indent);
          formatter.SetBeforeAfter(stmt.EndTok, -1, -1, indent);
          break;
      }

      return true;
    }

    private void ApplyMatchFormatting(int indent, List<IToken> ownedTokens) {
      var authorizeFlattening = false;
      var matchCaseNoIndent = false;
      var caseIndent = indent;
      var afterArrowIndent = indent + 2;
      foreach (var token in ownedTokens) {
        switch (token.val) {
          case "match":
            formatter.SetOpeningIndentedRegion(token, indent);
            break;
          case "{":
            caseIndent = indent + 2;
            afterArrowIndent = indent + 4;
            formatter.SetDelimiterIndentedRegions(token, indent);
            break;
          case "}":
            formatter.SetClosingIndentedRegion(token, indent);
            break;
          case "case":
            formatter.SetDelimiterIndentedRegions(token, caseIndent);
            break;
          case "=>":
            if (IsFollowedByNewline(token)) {
              formatter.SetBeforeAfter(token, afterArrowIndent, afterArrowIndent, afterArrowIndent);
            } else {
              formatter.SetBeforeAfter(token, afterArrowIndent, afterArrowIndent, -1);
              var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
              formatter.SetBeforeAfter(token, -1, -1, rightIndent);
            }

            break;
        }
      }
    }

    private bool ApplyITEFormatting(int indent, List<IToken> ownedTokens) {
      foreach (var token in ownedTokens) {
        switch (token.val) {
          case "if": {
              if (IsFollowedByNewline(token)) {
                formatter.SetOpeningIndentedRegion(token, indent);
              } else {
                var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
                formatter.SetBeforeAfter(token, indent, indent, rightIndent);
              }

              break;
            }
          case "else":
          case "then": {
              if (IsFollowedByNewline(token)) {
                formatter.SetOpeningIndentedRegion(token, indent);
              } else {
                var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
                formatter.SetBeforeAfter(token, indent, indent, rightIndent);
              }
              break;
            }
        }
      }

      return true;
    }

    private void ApplyVarAssignFormatting(int indent, List<IToken> ownedTokens) {
      var authorizeFlattening = false;
      var commaIndent = indent + 2;
      foreach (var token in ownedTokens) {
        switch (token.val) {
          case "var":
            if (IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indent);
              authorizeFlattening = true;
            } else {
              var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
              commaIndent = formatter.GetRightAlignIndentDelimiter(token, indent);
              formatter.SetBeforeAfter(token, indent, indent, rightIndent);
            }

            break;
          case ",":
            if (authorizeFlattening) {
              formatter.SetDelimiterInsideIndentedRegions(token, indent);
            } else {
              formatter.SetDelimiterIndentedRegions(token, commaIndent);
            }

            break;
          case ":|":
          case ":-":
          case ":=":
            if (!IsFollowedByNewline(token)) {
              formatter.SetBeforeAfter(token, indent + 2, indent + 2, -1);
              var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
              commaIndent = formatter.GetRightAlignIndentDelimiter(token, indent);
              formatter.SetBeforeAfter(token, -1, -1, rightIndent);
              authorizeFlattening = false;
            } else {
              authorizeFlattening = true;
              formatter.SetDelimiterInsideIndentedRegions(token, indent);
            }

            break;
          case ";":
            formatter.SetClosingIndentedRegionInside(token, indent);
            break;
            // Otherwise, these are identifiers, We don't need to specify their indentation.
        }
      }
    }

    private void FormatLikeLoop(List<IToken> ownedTokens, Statement body, int indent) {
      if (ownedTokens.Count > 0) {
        formatter.SetOpeningIndentedRegion(ownedTokens[0], indent);
      }

      for (var i = 1; i < ownedTokens.Count; i++) {
        formatter.SetOpeningIndentedRegion(ownedTokens[i], indent + 2);
      }

      formatter.SetDelimiterIndentedRegions(body.Tok, indent);
      formatter.SetClosingIndentedRegion(body.EndTok, indent);
    }

    protected override bool VisitOneExpr(Expression expr, ref int unusedIndent) {
      var firstToken = expr.StartToken;
      var indent = formatter.GetIndentBefore(firstToken);
      switch (expr) {
        case BinaryExpr binaryExpr: {
            ApplyBinaryExprFormatting(binaryExpr);
            break;
          }
        case LetExpr: {
            ApplyVarAssignFormatting(indent, expr.OwnedTokens);
            break;
          }
        case ITEExpr: {
            ApplyITEFormatting(indent, expr.OwnedTokens);
            break;
          }
        case NestedMatchExpr: {
            ApplyMatchFormatting(indent, expr.OwnedTokens);
            break;
          }
        case QuantifierExpr:
          break; // TODO
      }

      return true;
    }

    private void ApplyBinaryExprFormatting(BinaryExpr binaryExpr) {
      int indent;
      if (binaryExpr.Op is BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or) {
        // Alignment required.
        if (binaryExpr.OwnedTokens.Count == 2) {
          var firstToken = binaryExpr.OwnedTokens[0];
          var secondToken = binaryExpr.OwnedTokens[1];
          indent = formatter.GetTokenCol(firstToken, formatter.GetIndentBefore(firstToken)) - 1;
          var c = 0;
          while (c < firstToken.TrailingTrivia.Length && firstToken.TrailingTrivia[c] == ' ') {
            c++;
          }

          var conjunctExtraIndent = c + 2;
          binOpIndent = indent;
          binOpArgIndent = indent + conjunctExtraIndent;
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
    }
  }


  /// For example, the "if" keyword in the context of a statement
  ///
  /// // Not indented
  /// if       // line not indented
  ///   x == 2 // Line indented
  private void SetOpeningIndentedRegion(IToken token, int indent) {
    SetBeforeAfter(token, indent, indent, indent + 2);
  }

  /// For example, a "else" keyword in an expression
  ///
  /// if true then
  ///   1
  ///   // indented
  /// else     // line not indented
  ///   x == 2 // Line indented
  private void SetDelimiterIndentedRegions(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent, indent + 2);
  }

  /// For example, a ":=" token in an update statement
  ///
  /// x, y
  ///   // indented
  ///   := // indented
  ///   // indented
  ///   1, 2
  /// 
  private void SetDelimiterInsideIndentedRegions(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent + 2, indent + 2);
  }

  /// For example, a closing brace
  ///
  /// if true {
  ///   // indented
  /// } // not indented
  /// // not indented
  private void SetClosingIndentedRegion(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent, indent);
  }

  /// For example, a semicolon
  ///
  /// var x := 2
  ///   // indented
  ///   ; // indented
  /// // not indented
  private void SetClosingIndentedRegionInside(IToken token, int indent) {
    SetBeforeAfter(token, indent + 2, indent + 2, indent);
  }


  /// For example, a "else" keyword for a statement
  ///
  /// if x == 2 {
  /// }
  /// // not indented
  /// else // not indented
  /// // not indented
  /// {
  /// }
  /// // not indented
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
