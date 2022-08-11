using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.Serialization;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny.Triggers;
using Microsoft.VisualBasic;

namespace Microsoft.Dafny.Helpers;

public class HelperString {
  // If we ever decide that blank lines shouldn't have spaces, we can set this to true. 
  public static bool BlankNewlinesWithoutSpaces = true;

  // If we remove whitespace (tabs or space) at the end of lines. 
  public static bool RemoveTrailingWhitespace = true;

  public static bool Debug = false;

  public static bool FinishesByNewline(string s) {
    return s.Length > 0 && (s[^1] is '\n' or '\r');
  }

  public static readonly Regex NewlineRegex =
    new(@"(?<=(?<previousChar>\r?\n|\r(?!\n)|^))(?<currentIndent>[ \t]*)(?<commentType>/\*[\s\S]*\*\/|//|\r?\n|\r(?!\n)|$)|(?<=\S|^)(?<trailingWhitespace>[ \t]+)(?=\r?\n|\r(?!\n))");

  /// Given a space around a token (input),
  /// * precededByNewline means it's a leading space that was preceded by a newline
  /// or a trailing (isLeadingSpace==false)
  /// changes the indentation so that on the lines before, it uses indentationBefore,
  /// and on the last line it uses lastIndentation
  /// If it's a trailing space, no indentation is added after the last \n because it would be handled by the next leading space.
  public static string Reindent(string input, bool trailingTrivia, bool precededByNewline, string indentationBefore, string lastIndentation) {
    var commentExtra = "";
    // Invariant: Relative indentation inside a multi-line comment should be unchanged

    return NewlineRegex.Replace(input,
      MaybeDebug(trailingTrivia, match => {
        if (match.Groups["trailingWhitespace"].Success) {
          return RemoveTrailingWhitespace ? "" : match.Groups["trailingWhitespace"].Value;
        }

        var startOfString = match.Groups["previousChar"].Value == "";
        var commentType = match.Groups["commentType"].Value;
        if (startOfString && !precededByNewline) {
          if (RemoveTrailingWhitespace && commentType.StartsWith("\r") || commentType.StartsWith("\n")) {
            precededByNewline = true;
            return commentType;
          }
          return match.Groups[0].Value;
        }

        if (commentType.Length == 0) {//End of the string. Do we indent or not?
          return precededByNewline && !trailingTrivia ? lastIndentation : match.Groups[0].Value;
        }

        if (!startOfString) {
          precededByNewline = true;
        }

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

        // Last line
        return lastIndentation;
      })
    );
  }

  private static MatchEvaluator MaybeDebug(bool trailingTrivia, MatchEvaluator func) {
    if (!Debug) {
      return func;
    } else {
      return (Match match) => trailingTrivia ? "[" + func(match) + "]" : "{" + func(match) + "}";
    }
  }
}

public class IndentationFormatter : TokenFormatter.ITokenIndentations {
  public static int SpaceTab = 2;

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
  private void SetIndentations(IToken token, int before = -1, int sameLineBefore = -1, int after = -1) {
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

  // functions, methods, predicates, iterators...
  void SetMethodLikeIndent(IToken startToken, IEnumerable<IToken> ownedTokens, int indent) {
    var indent2 = indent + SpaceTab;
    if (startToken.val != "{") {
      SetIndentations(startToken, indent, indent, indent2);
    }
    var rightIndent = indent2 + SpaceTab;
    var commaIndent = indent2;
    foreach (var token in ownedTokens) {
      if (token.val is "{") {
        SetDelimiterIndentedRegions(token, indent);
      }
      if (token.val is "<" or "[" or "(") {
        if (IsFollowedByNewline(token)) {
          rightIndent = indent2 + SpaceTab;
          commaIndent = indent2;
          SetIndentations(token, commaIndent, commaIndent, rightIndent);
        } else {
          // Align capabilities
          SetAlign(indent2, token, out rightIndent, out commaIndent);
        }
      }
      if (token.val is ",") {
        SetIndentations(token, rightIndent, commaIndent, rightIndent);
      }
      if (token.val is ">" or "]" or ")") {
        SetIndentations(token, rightIndent, indent2, indent2);
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

  void SetTypeIndentation(Type type) {
    var tokens = type.OwnedTokens;
    if (tokens.Count == 0) {
      return;
    }

    var indent = GetIndentBefore(tokens[0]);
    if (tokens.Count > 1) {
      SetIndentations(tokens[0], after: indent + 2);
    }

    var commaIndent = indent + 2;
    var rightIndent = indent + 2;
    foreach (var token in tokens) {
      switch (token.val) {
        case "<": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent);
            } else {
              SetAlign(indent + SpaceTab, token, out rightIndent, out commaIndent);
            }
            break;
          }
        case ",": {
            SetIndentations(token, rightIndent, commaIndent, rightIndent);
            break;
          }
        case ">": {
            SetClosingIndentedRegionAligned(token, rightIndent, indent);
            break;
          }
      }
    }

    if (type is UserDefinedType userDefinedType) {
      foreach (var subtype in userDefinedType.TypeArgs) {
        SetTypeIndentation(subtype);
      }
    }
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
    SetMethodLikeIndent(member.StartToken, member.OwnedTokens, indent);
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
            var commaIndent = indent + SpaceTab;
            var rightIndent = indent + SpaceTab;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case ":=": {
                    if (IsFollowedByNewline(token)) {
                      SetDelimiterInsideIndentedRegions(token, indent);
                    } else {
                      SetAlign(indent + SpaceTab, token, out rightIndent, out commaIndent);
                    }
                    break;
                  }
                case ",": {
                    SetIndentations(token, rightIndent, commaIndent, rightIndent);
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
          SetFormalsIndentation(method.Ins);
          SetFormalsIndentation(method.Outs);
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
          SetFormalsIndentation(function.Formals);
          if (function.Result is { } outFormal) {
            SetTypeIndentation(outFormal.SyntacticType);
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
      SetIndentations(member.BodyEndTok, indent + SpaceTab, indent, indent);
    }

    PosToIndentAfter[member.EndToken.pos] = indent;
  }

  private void SetDeclIndentation(TopLevelDecl topLevelDecl, int indent) {
    var indent2 = indent + SpaceTab;
    if (topLevelDecl.StartToken.line > 0) {
      SetDelimiterIndentedRegions(topLevelDecl.BodyStartTok, indent);
      SetOpeningIndentedRegion(topLevelDecl.StartToken, indent);
    }

    if (topLevelDecl is AliasModuleDecl aliasModuleDecl) {
      SetAliasModuleDeclIndent(aliasModuleDecl, indent);
    } else if (topLevelDecl is ModuleExportDecl moduleExportDecl) {
      SetModuleExportDeclIndentation(moduleExportDecl, indent);
    } else if (topLevelDecl is AbstractModuleDecl abstractModuleDecl) {
      SetAbstractModuleDecl(abstractModuleDecl, indent);
    } else if (topLevelDecl is LiteralModuleDecl moduleDecl) {
      SetLiteralModuleDeclIndent(moduleDecl, indent);
    } else if (topLevelDecl is TopLevelDeclWithMembers declWithMembers) {
      if (declWithMembers is DatatypeDecl datatypeDecl) {
        SetDatatypeDeclIndent(indent, datatypeDecl);
      } else if (declWithMembers is RedirectingTypeDecl redirectingTypeDecl) {
        SetRedirectingTypeDeclDeclIndentation(indent, redirectingTypeDecl);
      } else if (topLevelDecl is IteratorDecl iteratorDecl) {
        SetIteratorDeclIndent(indent, iteratorDecl);
        if (iteratorDecl.BodyStartTok.line > 0) {
          SetDelimiterIndentedRegions(iteratorDecl.BodyStartTok, indent);
          SetClosingIndentedRegion(iteratorDecl.BodyEndTok, indent);
        }
        if (iteratorDecl.Body != null) {
          SetStatementIndentation(iteratorDecl.Body);
        }
      }

      var initialMemberIndent = declWithMembers.tok.line == 0 ? indent : indent2;
      foreach (var member in declWithMembers.Members) {
        SetMemberIndentation(member, initialMemberIndent);
      }
    } else if (topLevelDecl is SubsetTypeDecl subsetTypeDecl) {
      SetRedirectingTypeDeclDeclIndentation(indent, subsetTypeDecl);
    }

    if (topLevelDecl.StartToken.line > 0 && topLevelDecl.EndToken.val == "}") {
      SetIndentations(topLevelDecl.EndToken, indent2, indent, indent);
    }
  }

  private void SetIteratorDeclIndent(int indent, IteratorDecl iteratorDecl) {
    SetMethodLikeIndent(iteratorDecl.StartToken, iteratorDecl.OwnedTokens, indent);
  }

  private void SetModuleExportDeclIndentation(ModuleExportDecl moduleDecl, int indent) {
    var indentedFirst = false;
    var innerIndent = indent + SpaceTab;
    var revealExportIndent = innerIndent + SpaceTab;
    var commaIndent = innerIndent;
    foreach (var token in moduleDecl.OwnedTokens) {
      switch (token.val) {
        case "export": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "extends":
        case "reveals":
        case "provides": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, innerIndent);
              revealExportIndent = innerIndent + SpaceTab;
              commaIndent = innerIndent + SpaceTab;
            } else {
              SetAlign(innerIndent, token, out revealExportIndent, out commaIndent);
            }
            break;
          }
        case ",": {
            SetIndentations(token, before: revealExportIndent, sameLineBefore: commaIndent, after: revealExportIndent);
            break;
          }
      }
    }
  }

  private void SetAliasModuleDeclIndent(AliasModuleDecl moduleDecl, int indent) {
    var indentedFirst = false;
    foreach (var token in moduleDecl.OwnedTokens) {
      switch (token.val) {
        case "import":
        case "opened": {
            if (!indentedFirst) {
              SetOpeningIndentedRegion(token, indent);
              indentedFirst = true;
            }

            break;
          }
        case "=": {
            break;
          }
      }
    }
  }

  private void SetAbstractModuleDecl(AbstractModuleDecl moduleDecl, int indent) {
    var innerIndent = SetModuleDeclIndent(moduleDecl.OwnedTokens, indent);
  }

  private void SetLiteralModuleDeclIndent(LiteralModuleDecl moduleDecl, int indent) {
    var innerIndent = SetModuleDeclIndent(moduleDecl.OwnedTokens, indent);
    foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
      SetDeclIndentation(decl2, innerIndent);
    }
  }

  private int SetModuleDeclIndent(List<IToken> ownedTokens, int indent) {
    var innerIndent = indent + SpaceTab;
    var indentedFirst = false;
    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "abstract":
        case "module": {
            if (!indentedFirst) {
              SetOpeningIndentedRegion(token, indent);
              indentedFirst = true;
            }

            break;
          }
        case "{": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent);
            } else {
              SetAlign(indent, token, out innerIndent, out _);
            }

            break;
          }
        case "}": {
            SetClosingIndentedRegionAligned(token, innerIndent, indent);
            break;
          }
      }
    }

    return innerIndent;
  }

  private void SetRedirectingTypeDeclDeclIndentation(int indent, RedirectingTypeDecl typeSynonymDecl) {
    SetOpeningIndentedRegion(typeSynonymDecl.StartToken, indent);
    var indent2 = indent + SpaceTab;
    var rightOfVerticalBarIndent = indent2;
    var verticalBarIndent = indent2;
    foreach (var token in typeSynonymDecl.OwnedTokens) {
      switch (token.val) {
        case "newtype":
        case "type": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "=": {
            if (IsFollowedByNewline(token)) {
              SetDelimiterInsideIndentedRegions(token, indent);
            } else {
              SetAlign(indent2, token, out rightOfVerticalBarIndent, out verticalBarIndent);
            }

            break;
          }
        case "|": {
            SetIndentations(token, rightOfVerticalBarIndent, verticalBarIndent, rightOfVerticalBarIndent);
            break;
          }
        case "ghost": {
            SetIndentations(token, rightOfVerticalBarIndent, verticalBarIndent, verticalBarIndent);
            break;
          }
        case "witness": {
            if (rightOfVerticalBarIndent == indent2) {
              rightOfVerticalBarIndent = indent2 + SpaceTab;
            }
            SetIndentations(token, rightOfVerticalBarIndent, verticalBarIndent, rightOfVerticalBarIndent);
            break;
          }
        case "*": {
            // Nothing to add here.
            break;
          }
        case ";": {
            break;
          }
      }
    }

    if (typeSynonymDecl is SubsetTypeDecl subsetTypeDecl) {
      SetExpressionIndentation(subsetTypeDecl.Constraint);
      SetExpressionIndentation(subsetTypeDecl.Witness);
      SetTypeIndentation(subsetTypeDecl.Var.SyntacticType);
    } else if (typeSynonymDecl is NewtypeDecl newtypeDecl) {
      SetExpressionIndentation(newtypeDecl.Constraint);
      SetExpressionIndentation(newtypeDecl.Witness);
      SetTypeIndentation(newtypeDecl.Var.SyntacticType);
    }
  }

  private void SetDatatypeDeclIndent(int indent, DatatypeDecl datatypeDecl) {
    var indent2 = indent + SpaceTab;
    var verticalBarIndent = indent2;
    var rightOfVerticalBarIndent = indent2 + SpaceTab;
    var commaIndent = indent2;
    var rightIndent = indent2;
    foreach (var token in datatypeDecl.OwnedTokens) {
      switch (token.val) {
        case "datatype": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "=": {
            if (IsFollowedByNewline(token)) {
              SetDelimiterInsideIndentedRegions(token, indent2);
            } else {
              SetAlign(indent2, token, out rightOfVerticalBarIndent, out verticalBarIndent);
            }

            break;
          }
        case "|": {
            SetIndentations(token, rightOfVerticalBarIndent, verticalBarIndent, rightOfVerticalBarIndent);
            break;
          }
        case "(": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, rightOfVerticalBarIndent);
              commaIndent = rightOfVerticalBarIndent;
              rightIndent = commaIndent + SpaceTab;
            } else {
              SetAlign(rightOfVerticalBarIndent + SpaceTab, token, out rightIndent, out commaIndent);
            }

            break;
          }
        case ")": {
            SetIndentations(token.Prev, after: rightIndent);
            SetClosingIndentedRegionAligned(token, rightIndent, rightOfVerticalBarIndent);
            break;
          }
        case ",": {
            SetIndentations(token, rightIndent, commaIndent, rightIndent);
            break;
          }
        case ";": {
            break;
          }
      }
    }

    foreach (var ctor in datatypeDecl.Ctors) {
      SetFormalsIndentation(ctor.Formals);
    }
  }

  private void SetFormalsIndentation(List<Formal> ctorFormals) {
    foreach (var formal in ctorFormals) {
      SetTypeIndentation(formal.SyntacticType);
    }
  }

  public static IndentationFormatter ForProgram(Program program) {
    var indentationFormatter = new IndentationFormatter(
      new(),
      new(),
      new());

    foreach (var include in program.DefaultModuleDef.Includes) {
      if (include.OwnedTokens.Count > 0) {
        indentationFormatter.SetOpeningIndentedRegion(include.OwnedTokens[0], 0);
      }
    }

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
                formatter.SetOpeningIndentedRegion(ownedTokens[i], indent + SpaceTab);
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
            var rightIndent = indent + SpaceTab;
            var commaIndent = indent + SpaceTab;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case ",":
                  formatter.SetDelimiterSpeciallyIndentedRegions(token, commaIndent, rightIndent);
                  break;
                case ":|":
                case ":-":
                case ":=":
                  if (IsFollowedByNewline(token)) {
                    formatter.SetDelimiterInsideIndentedRegions(token, indent);
                  } else {
                    formatter.SetAlign(indent + SpaceTab, token, out rightIndent, out commaIndent);
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
            var commaIndent = indent + SpaceTab;
            var innerIndent = indent + SpaceTab;
            foreach (var token in ownedTokens) {
              switch (token.val) {
                case "reveal":
                case "print":
                  if (IsFollowedByNewline(token)) {
                    formatter.SetDelimiterInsideIndentedRegions(token, indent);
                  } else {
                    formatter.SetIndentations(token, indent, indent, -1);
                    innerIndent = formatter.GetRightAlignIndentAfter(token, indent);
                    commaIndent = formatter.GetRightAlignIndentDelimiter(token, indent);
                    formatter.SetIndentations(token, -1, -1, innerIndent);
                  }
                  formatter.SetOpeningIndentedRegion(token, indent);
                  break;
                case ",":
                  formatter.SetIndentations(token, innerIndent, commaIndent, innerIndent);
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
          formatter.SetMethodLikeIndent(stmt.Tok, stmt.OwnedTokens, indent);
          formatter.SetIndentations(stmt.EndTok, -1, -1, indent);
          break;
      }

      return true;
    }

    private void ApplyComprehensionExprFormatting(int indent, List<IToken> ownedTokens) {
      var afterAssignIndent = indent + SpaceTab;
      var alreadyAligned = false;
      var assignIndent = indent;

      foreach (var token in ownedTokens) {
        switch (token.val) {
          case "forall":
          case "exists":
          case "map":
          case "set":
          case "imap":
          case "iset": {
              formatter.SetOpeningIndentedRegion(token, indent);
              break;
            }
          case ":=":
          case "::": {
              if (alreadyAligned) {
                formatter.SetIndentations(token, afterAssignIndent, assignIndent, afterAssignIndent);
              } else {
                if (IsFollowedByNewline(token)) {
                  formatter.SetIndentations(token, afterAssignIndent, assignIndent, afterAssignIndent);
                } else {
                  alreadyAligned = true;
                  formatter.SetAlign(indent, token, out afterAssignIndent, out assignIndent);
                  assignIndent -= 1; // because "::" or ":=" has one more char than a comma 
                }
              }
              break;
            }
        }
      }
    }

    private void ApplyMatchFormatting(int indent, List<IToken> ownedTokens) {
      var matchCaseNoIndent = false;
      var caseIndent = indent;
      var afterArrowIndent = indent + SpaceTab;
      foreach (var token in ownedTokens) {
        switch (token.val) {
          case "match":
            formatter.SetOpeningIndentedRegion(token, indent);
            break;
          case "{":
            caseIndent = indent + SpaceTab;
            afterArrowIndent = caseIndent + SpaceTab;
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
              formatter.SetIndentations(token, afterArrowIndent, afterArrowIndent, afterArrowIndent);
            } else {
              formatter.SetIndentations(token, afterArrowIndent, afterArrowIndent);
              var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
              formatter.SetIndentations(token, after: rightIndent);
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
                formatter.SetAlignOpen(token, indent);
              }

              break;
            }
          case "else":
          case "then": {
              if (IsFollowedByNewline(token)) {
                formatter.SetOpeningIndentedRegion(token, indent);
              } else {
                var rightIndent = formatter.GetRightAlignIndentAfter(token, indent);
                formatter.SetIndentations(token, indent, indent, rightIndent);
              }
              break;
            }
        }
      }

      return true;
    }

    private void ApplyVarAssignFormatting(int indent, List<IToken> ownedTokens) {
      var commaIndent = indent + SpaceTab;
      var rightIndent = indent + SpaceTab;
      var semicolonIndent = indent;
      foreach (var token in ownedTokens) {
        switch (token.val) {
          case "var": {
              semicolonIndent = formatter.GetTokenCol(token, indent) - 1;
              if (IsFollowedByNewline(token)) {
                formatter.SetOpeningIndentedRegion(token, indent);
              } else {
                formatter.SetAlign(indent, token, out rightIndent, out commaIndent);
              }

              break;
            }
          case ",":
            formatter.SetDelimiterSpeciallyIndentedRegions(token, commaIndent, rightIndent);
            break;
          case ":|":
          case ":-":
          case ":=":
            if (!IsFollowedByNewline(token)) {
              formatter.SetAlign(indent + SpaceTab, token, out rightIndent, out commaIndent);
            } else {
              formatter.SetDelimiterInsideIndentedRegions(token, indent);
              commaIndent = indent + SpaceTab;
              rightIndent = indent + SpaceTab;
            }

            break;
          case ";":
            formatter.SetClosingIndentedRegionInside(token, semicolonIndent);
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
        formatter.SetOpeningIndentedRegion(ownedTokens[i], indent + SpaceTab);
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
        case ComprehensionExpr: {
            ApplyComprehensionExprFormatting(indent, expr.OwnedTokens);
            break;
          }
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

          var conjunctExtraIndent = c + SpaceTab;
          binOpIndent = indent;
          binOpArgIndent = indent + conjunctExtraIndent;
          formatter.SetIndentations(firstToken, binOpIndent, binOpIndent, binOpArgIndent);
          formatter.SetIndentations(secondToken, binOpIndent, binOpIndent, binOpArgIndent);
        } else {
          if (binOpIndent > 0) {
            formatter.SetIndentations(binaryExpr.OwnedTokens[0], binOpIndent, binOpIndent, binOpArgIndent);
          } else if (binaryExpr.OwnedTokens.Count > 0) {
            var startToken = binaryExpr.StartToken;
            var newIndent = formatter.GetTokenCol(startToken, formatter.GetIndentBefore(startToken)) - 1;
            formatter.SetIndentations(binaryExpr.OwnedTokens[0], newIndent, newIndent, newIndent);
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
    SetIndentations(token, indent, indent, indent + SpaceTab);
  }

  /// For example, a "," keyword in a specially indented list:
  ///
  /// var x, y :=   A()
  ///               // rightIndent
  ///           ,   // indent
  ///               // rightIndent
  ///               B();
  /// 
  private void SetDelimiterSpeciallyIndentedRegions(IToken token, int indent, int rightIndent) {
    SetIndentations(token, rightIndent, indent, rightIndent);
  }

  /// For example, a "else" keyword in an expression
  ///
  /// if true then
  ///   1
  ///   // indented
  /// else     // line not indented
  ///   x == 2 // Line indented
  private void SetDelimiterIndentedRegions(IToken token, int indent) {
    SetIndentations(token, indent + SpaceTab, indent, indent + SpaceTab);
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
    SetIndentations(token, indent + SpaceTab, indent + SpaceTab, indent + SpaceTab);
  }

  /// For example, a closing brace
  ///
  /// var x: map<   T
  ///           ,
  ///               U
  ///               // beforeIndent
  ///           >   // this line indent's
  ///           //  after liene indent
  /// // not indented
  private void SetClosingIndentedRegionAligned(IToken token, int beforeIndent, int indent) {
    SetIndentations(token, beforeIndent, indent, indent);
  }

  /// For example, a closing brace
  ///
  /// if true {
  ///   // indented
  /// } // not indented
  /// // not indented
  private void SetClosingIndentedRegion(IToken token, int indent) {
    SetIndentations(token, indent + SpaceTab, indent, indent);
  }

  /// For example, a semicolon
  ///
  /// var x := 2
  ///   // indented
  ///   ; // indented
  /// // not indented
  private void SetClosingIndentedRegionInside(IToken token, int indent) {
    SetIndentations(token, indent + SpaceTab, indent + SpaceTab, indent);
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
    SetIndentations(token, indent, indent, indent);
  }

  /// For example, an "equal" sign not followed by a space which indicates that things should be aligned
  ///
  /// var x, y :=    A()      //  The token ':=' is being considered
  ///           ,    B();
  /// ^indent and indentBefore
  ///                ^rightIndent
  ///           ^commaIndent
  /// 
  private void SetAlign(int indent, IToken token, out int rightIndent, out int commaIndent) {
    SetIndentations(token, indent, indent);
    rightIndent = GetRightAlignIndentAfter(token, indent);
    commaIndent = GetRightAlignIndentDelimiter(token, indent);
    SetIndentations(token, after: rightIndent);
  }

  /// For example, a "then" keyword not followed by a newline, indicating that the content should be aligned with the first character.
  ///
  /// if X
  /// then   proofY();
  ///        result
  /// ^indent
  ///        ^ rightIndent
  /// else Z
  /// 
  public void SetAlignOpen(IToken token, int indent) {
    var rightIndent = GetRightAlignIndentAfter(token, indent);
    SetIndentations(token, indent, indent, rightIndent);
  }

  private static readonly Dictionary<int, string> indentationsCache = new();

  private static string IndentationBy(int characters) {
    return indentationsCache.GetOrCreate(characters, () => new string(' ', characters));
  }

  public void GetIndentation(IToken token, string currentIndentation,
      out string indentationBefore, out bool indentationBeforeSet,
      out string lastIndentation, out bool lastIndentationSet,
      out string indentationAfter, out bool indentationAfterSet) {
    indentationBefore = currentIndentation;
    indentationBeforeSet = false;
    lastIndentation = currentIndentation;
    lastIndentationSet = false;
    indentationAfter = currentIndentation;
    indentationAfterSet = false;
    if (PosToIndentBefore.TryGetValue(token.pos, out var preIndentation)) {
      indentationBefore = IndentationBy(preIndentation);
      indentationBeforeSet = true;
      lastIndentation = indentationBefore;
      lastIndentationSet = true;
      indentationAfter = indentationBefore;
      indentationAfterSet = true;
    }
    if (PosToIndentLineBefore.TryGetValue(token.pos, out var sameLineIndentation)) {
      lastIndentation = IndentationBy(sameLineIndentation);
      lastIndentationSet = true;
      indentationAfter = lastIndentation;
      indentationAfterSet = true;
    }
    if (PosToIndentAfter.TryGetValue(token.pos, out var postIndentation)) {
      indentationAfter = IndentationBy(postIndentation);
      indentationAfterSet = true;
    }
  }
}