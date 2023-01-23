using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Formatting;
using Microsoft.VisualBasic;

namespace Microsoft.Dafny;

/** The first Dafny formatter
 * 
 * We want the guarantee that the reprinted program should be the same as the previous one, modulo whitespace.
 * Our approach in this formatter consists of three phases:
 * 1. Convert tokens to a double linked list so that we can traverse them from the beginning to the end and store the first token in the program (Scanner.frame, and all AST nodes)
 * 2. Traverse the program on pre-resolved nodes, and decide on the indentation of each token when it's associated to a declaration, a node, a statement, etc.
 * 3. Reprint the tokens in their original order by replacing their leading and trailing whitespace by their correctly indented counterpart
 *
 * Step 3. has been entirely written in Dafny, and offers the interesting guarantee that the final reprinted program will contain all the "val" of every token reachable from the first token provided in input.
 *
 * ## What is the indentation of a "token"?
 *
 * This formatter considers that each token has to be associated with 3 types of indentation.
 * 1. The indentation of comments that are before this token
 * 2. The indentation of this token itself if it starts a new line
 * 3. The indentation of comments and other non-marked tokens that are after this token.
 * 
 * Because the token printer will traverse the tokens in order, the indentation 1. is used only for the trivia associated to the token in the leading whitespace of that token, like `/* Comment about X * /` in the following example, which is in the leading trivia of `const`
 *
 * ```
 * datatype Y :=
 * | C
 * // Comment about C
 * | D
 * // Comment about D
 * 
 * /* Comment about X * /
 * const X := 2
 * ```
 * Note that in this same example, the indentation of `Comment about D` is possible because of the indentation stored in 3.
 * The indentation of 2. makes is possible to have the token to be a delimiter of two indented regions, like this:
 * 
 * ```dafny
 * if X then
 * Y
 * else // Here "else" has its own indentation
 * Z
 * ```
 */
public class IndentationFormatter : TopDownVisitor<int>, Formatting.IIndentationFormatter {

  /* If true, the indentation will be
   * var name := method(
   *   x,
   *   y
   * );
   * If false, the indentation will be
   * var name := method(
   *               x,
   *               y
   *             );
   */
  public bool ReduceBlockiness = true;

  private readonly int SpaceTab = 2;

  private readonly Dictionary<int, int> posToIndentBefore = new();
  private readonly Dictionary<int, int> posToIndentLineBefore = new();
  private readonly Dictionary<int, int> posToIndentAfter = new();

  // Used for bullet points && and ||
  private int binOpIndent = -1;
  private int binOpArgIndent = -1;


  private IndentationFormatter() {
    preResolve = true;
  }


  /// <summary>
  /// Creates an IndentationFormatter for the given program,
  /// by immediately processing all nodes and assigning indentations to most structural tokens 
  /// </summary>
  public static IndentationFormatter ForProgram(Program program, bool reduceBlockiness = true) {
    var indentationFormatter = new IndentationFormatter {
      ReduceBlockiness = reduceBlockiness
    };
    foreach (var include in program.DefaultModuleDef.Includes) {
      if (include.OwnedTokens.Any()) {
        indentationFormatter.SetOpeningIndentedRegion(include.OwnedTokens.First(), 0);
      }
    }

    foreach (var decl in program.DefaultModuleDef.TopLevelDecls) {
      indentationFormatter.SetDeclIndentation(decl, 0);
    }
    foreach (var decl in program.DefaultModuleDef.PrefixNamedModules) {
      indentationFormatter.SetDeclIndentation(decl.Item2, 0);
    }

    return indentationFormatter;
  }

  protected IEnumerable<Expression> SubExpressions(Expression expr) {
    return expr is ConcreteSyntaxExpression concreteSyntaxExpression
      ? concreteSyntaxExpression.PreResolveSubExpressions
      : expr.SubExpressions;
  }


  protected override bool VisitOneExpr(Expression expr, ref int unusedIndent) {
    if (expr == null) {
      return false;
    }
    var firstToken = expr.StartToken;
    var indent = GetIndentBefore(firstToken);
    switch (expr) {
      case ChainingExpression chainingExpr:
        return SetChainingExprIndent(indent, chainingExpr);
      case BinaryExpr binaryExpr:
        return SetBinaryExprIndent(indent, binaryExpr);
      case LetOrFailExpr:
      case LetExpr:
        return SetIndentVarDeclStmt(indent, expr.OwnedTokens, expr is LetOrFailExpr { Lhs: null }, true);
      case ITEExpr iteExpr:
        return SetIndentITE(indent, iteExpr);
      case NestedMatchExpr nestedMatchExpr:
        var i = unusedIndent;
        return SetIndentCases(indent, expr.OwnedTokens.Concat(nestedMatchExpr.Cases.SelectMany(oneCase => oneCase.OwnedTokens)), () => {
          foreach (var e in SubExpressions(expr)) {
            Visit(e, i);
          }
        });
      case LambdaExpr lambaExpression:
        return SetIndentLambdaExpr(indent, lambaExpression);
      case ComprehensionExpr:
        return SetIndentComprehensionExpr(indent, expr.OwnedTokens);
      case UnaryExpr:
      case OldExpr:
      case UnchangedExpr:
      case ParensExpression:
      case SeqDisplayExpr:
      case MapDisplayExpr:
      case SetDisplayExpr:
        return SetIndentParensExpression(indent, expr.OwnedTokens);
      case ApplySuffix applySuffix: {
          int reindent;
          if (ReduceBlockiness && applySuffix.StartToken.Prev.val is "=>" or ":=" or ":-" or ":|" && applySuffix.StartToken.Prev.line == applySuffix.StartToken.line) {
            var offset = applySuffix.StartToken.Prev.line == applySuffix.StartToken.Prev.Prev.line ? -SpaceTab : 0;
            reindent = Math.Max(GetIndentAfter(applySuffix.StartToken.Prev) + offset, 0);
          } else {
            reindent = GetNewTokenVisualIndent(applySuffix.StartToken, indent);
          }

          return SetIndentParensExpression(reindent, expr.OwnedTokens);
        }
      case StmtExpr stmtExpr: {
          return SetIndentStmtExpr(indent, stmtExpr);
        }
    }

    return true;
  }

  protected override bool VisitOneStmt(Statement stmt, ref int unusedIndent) {
    if (stmt == null) {
      return false;
    }
    var firstToken = stmt.Tok;
    var indent = GetIndentBefore(firstToken);
    // Every function returns if traverse needs to occur (true) or if it already happened (false) 
    switch (stmt) {
      case BlockStmt blockStmt:
        return SetIndentBlockStmt(indent, blockStmt);
      case IfStmt ifStmt:
        return SetIndentIfStmt(ifStmt, indent);
      case CalcStmt calcStmt:
        return SetIndentCalcStmt(indent, calcStmt);
      case SkeletonStatement:
        return true;
      case AlternativeStmt alternativeStmt:
        return SetIndentCases(indent, alternativeStmt.OwnedTokens.Concat(alternativeStmt.Alternatives.SelectMany(alternative => alternative.OwnedTokens)), () => {
          VisitAlternatives(alternativeStmt.Alternatives, indent);
        });
      case ForallStmt forallStmt: {
          SetIndentLikeLoop(forallStmt.OwnedTokens, forallStmt.Body, indent);
          foreach (var ens in forallStmt.Ens) {
            SetAttributedExpressionIndentation(ens, indent + SpaceTab);
          }

          SetClosingIndentedRegion(forallStmt.EndTok, indent);
          return false;
        }
      case WhileStmt whileStmt:
        return SetIndentWhileStmt(whileStmt, indent);
      case AlternativeLoopStmt alternativeLoopStmt:
        return SetIndentAlternativeLoopStmt(indent, alternativeLoopStmt);
      case ForLoopStmt forLoopStmt:
        return SetIndentForLoopStmt(forLoopStmt, indent);
      case VarDeclStmt varDeclStmt: {
          var result = SetIndentVarDeclStmt(indent, varDeclStmt.OwnedTokens, false, false);
          if (varDeclStmt.Update != null) {
            return SetIndentUpdateStmt(varDeclStmt.Update, indent, true);
          }

          return result;
        }
      case ConcreteUpdateStatement concreteUpdateStatement: {
          return SetIndentUpdateStmt(concreteUpdateStatement, indent, false);
        }
      case NestedMatchStmt:
        var i = unusedIndent;
        return SetIndentCases(indent, stmt.OwnedTokens, () => {
          foreach (var e in stmt.PreResolveSubExpressions) {
            Visit(e, i);
          }
          foreach (var s in stmt.PreResolveSubStatements) {
            Visit(s, i);
          }
        });
      case RevealStmt:
      case PrintStmt:
        return SetIndentPrintRevealStmt(indent, stmt);
      case AssumeStmt:
      case ExpectStmt:
      case AssertStmt:
        return SetIndentAssertLikeStatement(stmt, indent);
      case ModifyStmt modifyStmt:
        return SetIndentModifyStatement(modifyStmt, indent);

      default:
        SetMethodLikeIndent(stmt.Tok, stmt.OwnedTokens, indent);
        SetIndentations(stmt.EndTok, -1, -1, indent);
        break;
    }

    return true;
  }

  #region Access current indentation and already computed indentation, other helpers

  /// If the first token on the line of the given token satisfies the given predicate.
  /// Used to detect commented cases or datatype constructors
  private static bool FirstTokenOnLineIs(IToken token, Func<IToken, bool> predicate) {
    if (token.Prev == null || token.Prev.line != token.line) {
      return predicate(token);
    }
    return FirstTokenOnLineIs(token.Prev, predicate);
  }


  // Given a token, finds the indentation that was expected before it.
  // Used for frame expressions to initially copy the indentation of "reads", "requires", etc.
  private int GetIndentAfter(IToken token) {
    if (token == null) {
      return 0;
    }
    if (posToIndentAfter.TryGetValue(token.pos, out var indentation)) {
      return indentation;
    }
    return GetIndentAfter(token.Prev);
  }

  private int GetIndentBefore(IToken token) {
    if (posToIndentLineBefore.TryGetValue(token.pos, out var indentation)) {
      return indentation;
    }
    if (posToIndentBefore.TryGetValue(token.pos, out var indentation2)) {
      return indentation2;
    }
    return GetIndentAfter(token.Prev);
  }


  // Get the precise column this token will be at after reformatting.
  // Requires all tokens before to have been formatted.

  private int GetNewTokenVisualIndent(IToken token, int defaultIndent) {
    var previousTrivia = token.Prev != null ? token.Prev.TrailingTrivia : "";
    previousTrivia += token.LeadingTrivia;
    var lastNL = previousTrivia.LastIndexOf('\n');
    var lastCR = previousTrivia.LastIndexOf('\r');
    if (lastNL >= 0 || lastCR >= 0) {
      // If the leading trivia contains an inline comment after the last newline, it can change the position.
      var lastCharacterAfterNewline = Math.Max(lastNL, lastCR) + 1;
      var lastTrivia = previousTrivia.Substring(lastCharacterAfterNewline);
      if (lastTrivia.IndexOf("*/", StringComparison.Ordinal) >= 0) {
        return lastTrivia.Length;
      }
      if (posToIndentLineBefore.TryGetValue(token.pos, out var indentation)) {
        return indentation;
      }
      if (token.Prev != null &&
          posToIndentAfter.TryGetValue(token.Prev.pos, out var indentation2)) {
        return indentation2;
      }
      return defaultIndent;
    }
    // No newline, so no re-indentation.
    if (token.Prev != null) {
      return GetNewTokenVisualIndent(token.Prev, defaultIndent) + token.Prev.val.Length + previousTrivia.Length;
    }

    return token.col - 1;
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
    return GetNewTokenVisualIndent(token, indentFallback) + token.val.Length + trailingSpace;
  }

  private static readonly Regex FollowedByNewlineRegex = new Regex("^[ \t]*([\r\n]|//)");

  private static bool IsFollowedByNewline(IToken token) {
    return FollowedByNewlineRegex.IsMatch(token.TrailingTrivia);
  }

  #endregion

  #region All SetIndent* methods

  // 'before' is the hypothetical indentation of a comment before that token, and of the previous token if it does not have a set indentation
  // 'sameLineBefore' is the hypothetical indentation of this token if it was on its own line
  // 'after' is the hypothetical indentation of a comment after that token, and of the next token if it does not have a set indentation
  private void SetIndentations(IToken token, int before = -1, int sameLineBefore = -1, int after = -1) {
    if (token is IncludeToken || token.line == 0 && token.col == 0) { // Just ignore this token.
      return;
    }
    if (before >= 0) {
      posToIndentBefore[token.pos] = before;
    }

    if (sameLineBefore >= 0) {
      posToIndentLineBefore[token.pos] = sameLineBefore;
    }

    if (after >= 0) {
      posToIndentAfter[token.pos] = after;
    }
  }

  // functions, methods, predicates, iterators, can all be formatted using this method.
  // See FormatterWorksForMethodsInModule in Formatter.cs to see how methods are formatted.
  void SetMethodLikeIndent(IToken startToken, IEnumerable<IToken> ownedTokens, int indent) {
    var indent2 = indent + SpaceTab;
    if (startToken.val != "{") {
      SetIndentations(startToken, indent, indent, indent2);
    }
    var rightIndent = indent2 + SpaceTab;
    var commaIndent = indent2;
    var extraParenIndent = 0;
    var firstParensClosed = false;
    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "{":
          SetDelimiterIndentedRegions(token, indent);
          break;
        case "<" or "[" when IsFollowedByNewline(token):
          rightIndent = indent2 + SpaceTab;
          commaIndent = indent2;
          SetIndentations(token, commaIndent, commaIndent, rightIndent);
          break;
        case "<" or "[":
          // Align capabilities
          SetAlign(indent2, token, out rightIndent, out commaIndent);
          break;
        case "(" when IsFollowedByNewline(token):
          rightIndent = indent2 + extraParenIndent;
          commaIndent = indent + extraParenIndent;
          SetIndentations(token, commaIndent, commaIndent, rightIndent);
          break;
        case "(":
          // Align capabilities
          SetAlign(indent + extraParenIndent, token, out rightIndent, out commaIndent);
          break;
        case ",":
          SetIndentations(token, rightIndent, commaIndent, rightIndent);
          break;
        case ")":
          firstParensClosed = true;
          SetIndentations(token, rightIndent, indent + extraParenIndent, indent2);
          break;
        case ">" or "]":
          SetIndentations(token, rightIndent, indent2, indent2);
          break;
        case "}" when !posToIndentLineBefore.ContainsKey(token.pos):
          SetClosingIndentedRegion(token, indent);
          break;
        case "returns":
        case ":":
          if (firstParensClosed) {
            extraParenIndent = SpaceTab;
          }

          break;
        case "reads" or "modifies" or "decreases" or "requires" or "ensures" or "invariant" or "yield": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent2);
            } else {
              SetAlign(indent2, token, out rightIndent, out commaIndent);
              //SetIndentations(token, indent2, indent2, indent2 + token.val.Length + 1);
            }

            commaIndent = indent2;
            break;
          }
      }
    }
  }

  void SetTypeIndentation(Type type) {
    var tokens = type.OwnedTokens.ToList();
    if (!tokens.Any()) {
      return;
    }

    var indent = GetIndentBefore(tokens[0]);
    if (tokens.Count > 1) {
      SetIndentations(tokens[0], after: indent + 2);
    }

    var commaIndent = indent + 2;
    var rightIndent = indent + 2;
    var first = true;
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
    // Do attributes need special indentation rules
  }

  void SetDecreasesExpressionIndentation(Expression expression, int indent) {
    SetExpressionIndentation(expression);
    SetIndentations(expression.EndToken, after: indent);
  }

  void SetAttributedExpressionIndentation(AttributedExpression attrExpression, int indent) {
    SetAttributeIndentation(attrExpression.Attributes);
    SetExpressionIndentation(attrExpression.E);
    SetIndentations(attrExpression.E.EndToken, after: indent);
  }

  void SetFrameExpressionIndentation(FrameExpression frameExpression, int indent) {
    SetExpressionIndentation(frameExpression.E);
    SetIndentations(frameExpression.E.EndToken, after: indent);
  }

  void SetExpressionIndentation(Expression expression) {
    if (expression != null) {
      Visit(expression, GetIndentBefore(expression.StartToken));
    }
  }

  void SetStatementIndentation(Statement statement) {
    Visit(statement, 0);
  }

  private void SetFunctionIndentation(MemberDecl member, int indent, Function function) {
    SetMethodLikeIndent(member.StartToken, member.OwnedTokens, indent);
    if (member.BodyStartTok.line > 0) {
      SetDelimiterIndentedRegions(member.BodyStartTok, indent);
    }

    SetFormalsIndentation(function.Formals);
    if (function.Result is { } outFormal) {
      SetTypeIndentation(outFormal.SyntacticType);
    }

    foreach (var req in function.Req) {
      SetAttributedExpressionIndentation(req, indent + SpaceTab);
    }

    foreach (var frame in function.Reads) {
      SetFrameExpressionIndentation(frame, indent + SpaceTab);
    }

    foreach (var ens in function.Ens) {
      SetAttributedExpressionIndentation(ens, indent + SpaceTab);
    }

    foreach (var dec in function.Decreases.Expressions) {
      SetDecreasesExpressionIndentation(dec, indent + SpaceTab);
    }

    if (function.ByMethodBody is { } byMethodBody) {
      SetDelimiterIndentedRegions(byMethodBody.StartToken, indent);
      SetClosingIndentedRegion(byMethodBody.EndTok, indent);
      SetStatementIndentation(byMethodBody);
    }

    SetExpressionIndentation(function.Body);
  }

  private void SetMethodIndentation(int indent, Method method) {
    SetMethodLikeIndent(method.StartToken, method.OwnedTokens, indent);
    if (method.BodyStartTok.line > 0) {
      SetDelimiterIndentedRegions(method.BodyStartTok, indent);
    }

    SetFormalsIndentation(method.Ins);
    SetFormalsIndentation(method.Outs);
    foreach (var req in method.Req) {
      SetAttributedExpressionIndentation(req, indent + SpaceTab);
    }

    foreach (var mod in method.Mod.Expressions) {
      SetFrameExpressionIndentation(mod, indent + SpaceTab);
    }

    foreach (var ens in method.Ens) {
      SetAttributedExpressionIndentation(ens, indent + SpaceTab);
    }

    foreach (var dec in method.Decreases.Expressions) {
      SetDecreasesExpressionIndentation(dec, indent + SpaceTab);
      SetExpressionIndentation(dec);
    }

    if (method.Body != null) {
      SetStatementIndentation(method.Body);
    }
  }

  private void SetFieldIndentation(int indent, Field field) {
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
  }

  private void SetDeclIndentation(TopLevelDecl topLevelDecl, int indent) {
    if (topLevelDecl.tok is IncludeToken) {
      return;
    }
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
      if (declWithMembers is OpaqueTypeDecl opaqueTypeDecl) {
        SetOpaqueTypeDeclIndent(indent, opaqueTypeDecl);
      } else if (declWithMembers is DatatypeDecl datatypeDecl) {
        SetDatatypeDeclIndent(indent, datatypeDecl);
      } else if (declWithMembers is RedirectingTypeDecl redirectingTypeDecl) {
        SetRedirectingTypeDeclDeclIndentation(indent, redirectingTypeDecl);
      } else if (topLevelDecl is IteratorDecl iteratorDecl) {
        SetIteratorDeclIndent(indent, iteratorDecl);
      } else if (topLevelDecl is ClassDecl classDecl) {
        SetClassDeclIndent(indent, classDecl);
      }

      var initialMemberIndent = declWithMembers.tok.line == 0 ? indent : indent2;
      foreach (var member in declWithMembers.Members) {
        if (member.tok is IncludeToken) {
          continue;
        }
        SetMemberIndentation(member, initialMemberIndent);
      }
    } else if (topLevelDecl is SubsetTypeDecl subsetTypeDecl) {
      SetRedirectingTypeDeclDeclIndentation(indent, subsetTypeDecl);
    } else if (topLevelDecl is TypeSynonymDecl typeSynonymDecl) {
      SetRedirectingTypeDeclDeclIndentation(indent, typeSynonymDecl);
    }

    if (topLevelDecl.StartToken.line > 0 && topLevelDecl.EndToken.val == "}") {
      SetIndentations(topLevelDecl.EndToken, indent2, indent, indent);
    }
  }

  private void SetMemberIndentation(MemberDecl member, int indent) {
    switch (member) {
      case Field field: {
          SetFieldIndentation(indent, field);
          break;
        }

      case Method method: {
          SetMethodIndentation(indent, method);
          break;
        }
      case Function function: {
          SetFunctionIndentation(member, indent, function);
          break;
        }
      default: {
          SetMethodLikeIndent(member.StartToken, member.OwnedTokens, indent);
          if (member.BodyStartTok.line > 0) {
            SetDelimiterIndentedRegions(member.BodyStartTok, indent);
          }
          break;
        }
    }
    if (member.BodyEndTok.line > 0) {
      SetIndentations(member.BodyEndTok, indent + SpaceTab, indent, indent);
    }

    posToIndentAfter[member.EndToken.pos] = indent;
  }

  private void SetIteratorDeclIndent(int indent, IteratorDecl iteratorDecl) {
    SetMethodLikeIndent(iteratorDecl.StartToken, iteratorDecl.OwnedTokens, indent);
    foreach (var req in iteratorDecl.Requires) {
      SetAttributedExpressionIndentation(req, indent + SpaceTab);
    }
    foreach (var req in iteratorDecl.Ensures) {
      SetAttributedExpressionIndentation(req, indent + SpaceTab);
    }
    foreach (var req in iteratorDecl.YieldRequires) {
      SetAttributedExpressionIndentation(req, indent + SpaceTab);
    }
    foreach (var req in iteratorDecl.YieldEnsures) {
      SetAttributedExpressionIndentation(req, indent + SpaceTab);
    }
    SetFormalsIndentation(iteratorDecl.Ins);
    SetFormalsIndentation(iteratorDecl.Outs);
    if (iteratorDecl.BodyStartTok.line > 0) {
      SetDelimiterIndentedRegions(iteratorDecl.BodyStartTok, indent);
      SetClosingIndentedRegion(iteratorDecl.BodyEndTok, indent);
    }
    if (iteratorDecl.Body != null) {
      SetStatementIndentation(iteratorDecl.Body);
    }
  }

  private void SetClassDeclIndent(int indent, ClassDecl classDecl) {
    IToken classToken = null;
    IToken extendsToken = null;
    var parentTraitIndent = indent + SpaceTab;
    var commaIndent = indent;
    var extraIndent = 0;
    var ownedTokens = classDecl.OwnedTokens;

    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "class": {
            classToken = token;
            break;
          }
        case "extends": {
            extendsToken = token;
            if (extendsToken.line != extendsToken.Next.line) {
              extraIndent = classToken != null && classToken.line == extendsToken.line ? 0 : SpaceTab;
              commaIndent += extraIndent;
              SetIndentations(extendsToken, after: indent + SpaceTab + extraIndent);
            } else {
              extraIndent += 2;
              commaIndent = indent + SpaceTab;
              SetIndentations(extendsToken, after: indent + SpaceTab);
            }
            break;
          }
        case ",": {
            SetIndentations(token, parentTraitIndent + extraIndent, commaIndent, parentTraitIndent + extraIndent);
            break;
          }
      }
    }
    foreach (var parent in classDecl.ParentTraits) {
      SetTypeIndentation(parent);
    }
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
    foreach (var token in moduleDecl.OwnedTokens) {
      switch (token.val) {
        case "import": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case ":": {
            break;
          }
      }
    }
  }

  private void SetLiteralModuleDeclIndent(LiteralModuleDecl moduleDecl, int indent) {
    var innerIndent = SetModuleDeclIndent(moduleDecl.OwnedTokens, indent);
    foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
      SetDeclIndentation(decl2, innerIndent);
    }
    foreach (var decl2 in moduleDecl.ModuleDef.PrefixNamedModules) {
      SetDeclIndentation(decl2.Item2, innerIndent);
    }
  }

  private int SetModuleDeclIndent(IEnumerable<IToken> ownedTokens, int indent) {
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

  private void SetRedirectingTypeDeclDeclIndentation(int indent, RedirectingTypeDecl redirectingTypeDecl) {
    SetOpeningIndentedRegion(redirectingTypeDecl.StartToken, indent);
    var indent2 = indent + SpaceTab;
    var rightOfVerticalBarIndent = indent2 + SpaceTab;
    var verticalBarIndent = indent2;
    foreach (var token in redirectingTypeDecl.OwnedTokens) {
      switch (token.val) {
        case "newtype":
        case "type": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "=": {
            SetDelimiterInsideIndentedRegions(token, indent);
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
        case "{": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "}": {
            SetClosingIndentedRegion(token, indent);
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

    if (redirectingTypeDecl is SubsetTypeDecl subsetTypeDecl) {
      SetExpressionIndentation(subsetTypeDecl.Constraint);
      SetExpressionIndentation(subsetTypeDecl.Witness);
      SetTypeIndentation(subsetTypeDecl.Var.SyntacticType);
      SetIndentations(subsetTypeDecl.EndToken, after: indent);
    } else if (redirectingTypeDecl is NewtypeDecl newtypeDecl) {
      SetExpressionIndentation(newtypeDecl.Constraint);
      SetExpressionIndentation(newtypeDecl.Witness);
      if (newtypeDecl.Var != null) {
        SetTypeIndentation(newtypeDecl.Var.SyntacticType);
      }
      SetIndentations(newtypeDecl.EndToken, after: indent);
    } else if (redirectingTypeDecl is TypeSynonymDecl typeSynonymDecl) {
      SetIndentations(typeSynonymDecl.EndToken, after: indent);
    }
  }

  private void SetOpaqueTypeDeclIndent(int indent, OpaqueTypeDecl opaqueTypeDecl) {
    var indent2 = indent + SpaceTab;
    var typeArgumentIndent = indent2;
    var commaIndent = indent2;
    var rightIndent = indent2;
    foreach (var token in opaqueTypeDecl.OwnedTokens) {
      switch (token.val) {
        case "type": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "=": {
            if (IsFollowedByNewline(token)) {
              SetDelimiterInsideIndentedRegions(token, indent2);
            } else {
              SetAlign(indent2, token, out typeArgumentIndent, out _);
            }

            break;
          }
        case "<": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, typeArgumentIndent);
              commaIndent = typeArgumentIndent;
              rightIndent = commaIndent + SpaceTab;
            } else {
              SetAlign(typeArgumentIndent + SpaceTab, token, out rightIndent, out commaIndent);
            }

            break;
          }
        case ">": {
            SetIndentations(token.Prev, after: rightIndent);
            SetClosingIndentedRegionAligned(token, rightIndent, typeArgumentIndent);
            break;
          }
        case ",": {
            SetIndentations(token, rightIndent, commaIndent, rightIndent);
            break;
          }
        case ";": {
            break;
          }
        case "{": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "}": {
            SetClosingIndentedRegion(token, indent);
            break;
          }
      }
    }

    if (opaqueTypeDecl.EndToken.TrailingTrivia.Trim() == "") {
      SetIndentations(opaqueTypeDecl.EndToken, after: indent);
    }
  }

  private void SetDatatypeDeclIndent(int indent, DatatypeDecl datatypeDecl) {
    var indent2 = indent + SpaceTab;
    var verticalBarIndent = indent2;
    var rightOfVerticalBarIndent = indent2 + SpaceTab;
    if (datatypeDecl.OwnedTokens.All(token =>
          token.val != "|" || IsFollowedByNewline(token) || token.Next.line == token.Prev.line)) {
      rightOfVerticalBarIndent = indent2;
    }
    var commaIndent = indent2;
    var rightIndent = indent2;
    var noExtraIndent =
      ReduceBlockiness && datatypeDecl.Ctors.Count == 1
      && datatypeDecl.Ctors[0].Formals.Count > 0;
    if (noExtraIndent) {
      rightOfVerticalBarIndent = indent;
    }
    foreach (var token in datatypeDecl.OwnedTokens) {
      switch (token.val) {
        case "datatype": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "=": {
            if (IsFollowedByNewline(token) || noExtraIndent) {
              SetIndentations(token, rightOfVerticalBarIndent, indent + SpaceTab, rightOfVerticalBarIndent);
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
        case "{": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "}": {
            SetClosingIndentedRegion(token, indent);
            break;
          }
      }
    }

    foreach (var ctor in datatypeDecl.Ctors) {
      SetFormalsIndentation(ctor.Formals);
    }

    if (datatypeDecl.EndToken.TrailingTrivia.Trim() == "") {
      SetIndentations(datatypeDecl.EndToken, after: indent);
    }
  }

  private void SetFormalsIndentation(List<Formal> ctorFormals) {
    foreach (var formal in ctorFormals) {
      SetTypeIndentation(formal.SyntacticType);
    }
  }

  // All SetIndent* methods

  private bool SetIndentIfStmt(IfStmt ifStmt, int indent) {
    foreach (var token in ifStmt.OwnedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "if": {
            SetOpeningIndentedRegion(token, indent);
            Visit(ifStmt.Guard, indent);
            VisitBody(ifStmt.Thn, indent);
            break;
          }
        case "else": {
            SetKeywordWithoutSurroundingIndentation(token, indent);
            VisitBody(ifStmt.Els, indent);
            break;
          }
      }
    }
    return false;
  }

  private bool SetIndentModifyStatement(ModifyStmt stmt, int indent) {
    var ownedTokens = stmt.OwnedTokens;
    var commaIndent = indent + SpaceTab;
    var afterCommaIndent = commaIndent;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "modifies":
        case "modify":
          if (IsFollowedByNewline(token)) {
            SetOpeningIndentedRegion(token, indent);
          } else {
            SetAlign(indent, token, out afterCommaIndent, out commaIndent);
          }
          break;
        case ",":
          SetIndentations(token, afterCommaIndent, commaIndent, afterCommaIndent);
          break;
        case "{":
          SetOpeningIndentedRegion(token, indent);
          break;
        case "}":
        case ";":
          SetClosingIndentedRegion(token, indent);
          break;
      }
    }

    if (stmt.Body != null && stmt.Body.StartToken.line > 0) {
      SetOpeningIndentedRegion(stmt.Body.StartToken, indent);
    }

    return true;
  }

  private bool SetIndentAssertLikeStatement(Statement stmt, int indent) {
    var ownedTokens = stmt.OwnedTokens;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "assume":
        case "expect":
        case "assert":
          SetOpeningIndentedRegion(token, indent);
          break;
        case "}":
        case "by":
          SetClosingIndentedRegion(token, indent);
          break;
        case ";":
          SetClosingIndentedRegionInside(token, indent);
          break;
        case "{":
          SetOpeningIndentedRegion(token, indent);
          break;
      }
    }

    if (stmt is AssertStmt { Proof: { StartToken: { } startToken } }) {
      SetOpeningIndentedRegion(startToken, indent);
    }

    return true;
  }

  private bool SetIndentWhileStmt(WhileStmt whileStmt, int indent) {
    SetIndentLikeLoop(whileStmt.OwnedTokens, whileStmt.Body, indent);
    foreach (var ens in whileStmt.Invariants) {
      SetAttributedExpressionIndentation(ens, indent + SpaceTab);
    }

    foreach (var dec in whileStmt.Decreases.Expressions) {
      SetDecreasesExpressionIndentation(dec, indent + SpaceTab);
    }

    if (whileStmt.EndTok.val == "}") {
      SetClosingIndentedRegion(whileStmt.EndTok, indent);
    }

    return false;
  }

  private bool SetIndentAlternativeLoopStmt(int indent, AlternativeLoopStmt alternativeLoopStmt) {
    return SetIndentCases(indent, alternativeLoopStmt.OwnedTokens.Concat(alternativeLoopStmt.Alternatives.SelectMany(alternative => alternative.OwnedTokens)), () => {
      foreach (var ens in alternativeLoopStmt.Invariants) {
        SetAttributedExpressionIndentation(ens, indent + SpaceTab);
      }

      foreach (var dec in alternativeLoopStmt.Decreases.Expressions) {
        SetDecreasesExpressionIndentation(dec, indent + SpaceTab);
      }

      VisitAlternatives(alternativeLoopStmt.Alternatives, indent);
      if (alternativeLoopStmt.EndTok.val == "}") {
        SetClosingIndentedRegion(alternativeLoopStmt.EndTok, indent);
      }
    });
  }

  private bool SetIndentForLoopStmt(ForLoopStmt forLoopStmt, int indent) {
    var ownedTokens = forLoopStmt.OwnedTokens;
    var forReached = false;
    var specification = false;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      if (token.val == "for") {
        SetOpeningIndentedRegion(token, indent);
        forReached = true;
        continue;
      }

      if (!forReached) {
        continue;
      }

      if (specification) {
        SetOpeningIndentedRegion(token, indent + SpaceTab);
      }

      if (token.val == "to" || token.val == "downto") {
        specification = true;
      }
    }

    foreach (var ens in forLoopStmt.Invariants) {
      SetAttributedExpressionIndentation(ens, indent + SpaceTab);
    }

    VisitBody(forLoopStmt.Body, indent);
    SetClosingIndentedRegion(forLoopStmt.EndTok, indent);
    return false;
  }

  private bool SetIndentPrintRevealStmt(int indent, Statement stmt) {
    var ownedTokens = stmt.OwnedTokens;
    var commaIndent = indent + SpaceTab;
    var innerIndent = indent + SpaceTab;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "reveal":
        case "print":
          if (IsFollowedByNewline(token)) {
            SetOpeningIndentedRegion(token, indent);
          } else {
            SetAlign(indent, token, out innerIndent, out commaIndent);
          }
          break;
        case ",":
          SetIndentations(token, innerIndent, commaIndent, innerIndent);
          break;
        case ";":
          SetClosingIndentedRegionInside(token, indent);
          break;
      }
    }

    return true;
  }

  private bool SetIndentUpdateStmt(ConcreteUpdateStatement stmt, int indent, bool inner) {
    var ownedTokens = stmt.OwnedTokens.ToList();
    var opIndentDefault =
      stmt is AssignOrReturnStmt assignStmt && assignStmt.Lhss.Count == 0
        ? indent : indent + SpaceTab;
    var startToken = stmt.StartToken;
    int startIndent = inner ? indent + SpaceTab : indent;
    int afterStartIndent = indent + SpaceTab;
    var rightIndent = indent + SpaceTab;
    var commaIndent = indent + SpaceTab;
    SetIndentations(startToken, startIndent, startIndent, afterStartIndent);

    var rhss = stmt is UpdateStmt updateStmt ? updateStmt.Rhss
      : stmt is AssignOrReturnStmt assignOrReturnStmt ?
        new List<AssignmentRhs> { assignOrReturnStmt.Rhs }.Concat(assignOrReturnStmt.Rhss).ToList()
        : new List<AssignmentRhs>();

    // For single Rhs that are of the form [new] X(args....),
    // we can even further decrease the indent so that the last parenthesis
    // is aligned with the beginning of the declaration. 
    var singleRhs = rhss.Count == 1;

    void InferRightIndentFromRhs() {
      if (rhss.Any()) {
        var rhs = rhss[0];
        rightIndent = GetNewTokenVisualIndent(rhs.RangeToken.StartToken, rightIndent);
        if (rhs is TypeRhs or ExprRhs { Expr: ApplySuffix } && ReduceBlockiness) {
          rightIndent = afterStartIndent;
          commaIndent = rightIndent - SpaceTab;
          if (singleRhs && (
                rhs.StartToken.line == rhs.StartToken.Prev?.line
                || stmt.Lhss.Count == 0)) {
            rightIndent -= SpaceTab;
          }
        }
      }
    }

    if (!ownedTokens.Any(token => token.val == ":=" || token.val == ":-" || token.val == ":|")) {
      InferRightIndentFromRhs();
    }

    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, startIndent)) {
        continue;
      }
      switch (token.val) {
        case ",":
          SetDelimiterSpeciallyIndentedRegions(token, commaIndent, rightIndent);
          break;
        case ":|":
        case ":-":
        case ":=": {
            if (IsFollowedByNewline(token)) {
              if (startToken == token && !inner) {
                // True if it did not have a LHS
                SetOpeningIndentedRegion(token, indent);
              } else {
                SetDelimiterSpeciallyIndentedRegions(token, afterStartIndent, afterStartIndent);
              }
            } else {
              var opIndent = posToIndentLineBefore.ContainsKey(token.pos)
                ? posToIndentLineBefore[token.pos]
                : opIndentDefault;
              /*if (ReduceBlockiness) {
                commaIndent = indent + SpaceTab;
                rightIndent = commaIndent;
              } else {*/
              SetAlign(opIndent, token, out rightIndent, out commaIndent);
              //}
            }

            InferRightIndentFromRhs();

            break;
          }

        case ";":
          SetClosingIndentedRegionInside(token, indent);
          break;
          // Otherwise, these are identifiers, We don't need to specify their indentation.
      }
    }

    foreach (var rhs in rhss) {
      if (rhs is ExprRhs { Expr: ApplySuffix x }) {
        SetIndentParensExpression(rightIndent, x.OwnedTokens);
        foreach (var node in x.PreResolveSubExpressions) {
          Visit(node, rightIndent);
        }
      } else {
        SetIndentParensExpression(rightIndent, rhs.OwnedTokens);
        foreach (var node in rhs.PreResolveSubExpressions) {
          Visit(node, rightIndent);
        }
      }
    }

    return false;
  }

  private bool SetIndentBlockStmt(int indent, BlockStmt blockStmt) {
    var braceIndent = indent;
    var innerBlockIndent = indent + SpaceTab;
    foreach (var token in blockStmt.OwnedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "{": {
            if (!posToIndentLineBefore.ContainsKey(token.pos)) {
              SetDelimiterIndentedRegions(token, braceIndent);
            } else {
              braceIndent = posToIndentLineBefore[token.pos];
              if (!posToIndentBefore.ContainsKey(token.pos)) {
                SetDelimiterIndentedRegions(token, braceIndent);
              }

              if (!IsFollowedByNewline(token)) {
                // Align statements
                SetAlign(indent, token, out innerBlockIndent, out braceIndent);
              }
            }

            break;
          }
        case "}": {
            SetIndentations(token, braceIndent + SpaceTab, braceIndent, indent);
            break;
          }
      }
    }

    foreach (var blockStmtBody in blockStmt.Body) {
      if (blockStmtBody is not BlockStmt && blockStmt.OwnedTokens.Any()) {
        SetIndentations(blockStmtBody.StartToken, innerBlockIndent, innerBlockIndent);
      }

      Visit(blockStmtBody, indent + SpaceTab);
    }

    return false;
  }

  private bool SetIndentCalcStmt(int indent, CalcStmt calcStmt) {
    var inCalc = false;
    var inOrdinal = false;
    var first = true;
    var innerCalcIndent = indent + SpaceTab;
    var extraHintIndent = 0;
    var ownedTokens = calcStmt.OwnedTokens;
    // First phase: We get the alignment
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "calc":
        case ";":
        case "}": {
            break;
          }
        case "{": {
            inCalc = true;
            break;
          }
        default: {
            if (inCalc) {
              if (token.val == "[") {
                inOrdinal = true;
              }
              if (token.val == "]") {
                inOrdinal = false;
              }
              if (!IsFollowedByNewline(token) &&
                  (token.val != "==" || token.Next.val != "#") &&
                  token.val != "#" &&
                  !inOrdinal) {
                if (token.Next.val != "{") {
                  SetIndentations(token, sameLineBefore: indent);
                  innerCalcIndent = Math.Max(innerCalcIndent, GetRightAlignIndentAfter(token, indent));
                } else {// It's an hint! If there is no comment and no newline between them, we align the hints as well.
                  if ((token.TrailingTrivia + token.Next.LeadingTrivia).Trim() == "" &&
                      token.line == token.Next.line) {
                    extraHintIndent = Math.Max(extraHintIndent, GetRightAlignIndentAfter(token, indent) - (indent + SpaceTab));
                  }
                }
              }
            }

            break;
          }
      }
    }

    inCalc = false;
    foreach (var token in calcStmt.OwnedTokens) {
      switch (token.val) {
        case "calc": {
            break;
          }
        case "{": {
            SetIndentations(token, indent, indent, innerCalcIndent);
            inCalc = true;
            break;
          }
        case "}": {
            SetIndentations(token, innerCalcIndent, indent, indent);
            break;
          }
        case ";": {
            SetDelimiterInsideIndentedRegions(token, indent);
            break;
          }
        default: {
            // It has to be an operator
            if (inCalc) {
              SetIndentations(token, innerCalcIndent, indent, innerCalcIndent);
            }

            break;
          }
      }
    }

    foreach (var hint in calcStmt.Hints) {
      // This block
      if (hint.Tok.pos != hint.EndTok.pos) {
        foreach (var hintStep in hint.Body) {
          SetOpeningIndentedRegion(hintStep.StartToken, indent + SpaceTab + extraHintIndent);
        }
      }
    }

    foreach (var expression in calcStmt.Lines) {
      SetIndentations(expression.StartToken, innerCalcIndent, innerCalcIndent, innerCalcIndent);
    }

    return true;
  }

  private void VisitAlternatives(List<GuardedAlternative> alternatives, int indent) {
    foreach (var alternative in alternatives) {
      Visit(alternative.Guard, indent + SpaceTab);
      foreach (var bodyStmt in alternative.Body) {
        Visit(bodyStmt, indent + SpaceTab);
      }
    }
  }

  private void VisitBody(Statement body, int indent) {
    if (body == null) {
      return;
    }
    SetDelimiterIndentedRegions(body.Tok, indent);
    SetClosingIndentedRegion(body.EndTok, indent);
    Visit(body, indent);
  }

  private bool SetIndentLambdaExpr(int indent, LambdaExpr lambdaExpr) {
    var itemIndent = indent + SpaceTab;
    var commaIndent = indent;
    var firstSpec = true;
    var specIndent = indent + SpaceTab;
    foreach (var token in lambdaExpr.OwnedTokens) {
      switch (token.val) {
        case "(": {
            if (IsFollowedByNewline(token)) {
              SetIndentations(token, indent, indent, itemIndent);
            } else {
              SetAlign(indent, token, out itemIndent, out commaIndent);
            }

            break;
          }
        case ")": {
            SetIndentations(token, itemIndent, indent, itemIndent);
            break;
          }
        case ",": {
            SetIndentations(token, itemIndent, commaIndent, itemIndent);
            break;
          }
        case "requires":
        case "reads": {
            if (firstSpec) {
              specIndent = GetNewTokenVisualIndent(token, indent);
              firstSpec = false;
            }
            SetIndentations(token, specIndent, specIndent, specIndent + SpaceTab);
            break;
          }
        case "=>": {
            SetIndentations(token, itemIndent, indent, indent + SpaceTab);
            break;
          }
      }
    }

    foreach (var bv in lambdaExpr.BoundVars) {
      if (bv.SyntacticType != null) {
        SetTypeIndentation(bv.SyntacticType);
      }
    }

    return true;
  }

  private bool SetIndentStmtExpr(int indent, StmtExpr stmtExpr) {
    Visit(stmtExpr.S, indent);
    SetIndentations(stmtExpr.S.EndTok, after: indent);
    Visit(stmtExpr.E, indent);
    return false;
  }

  private bool SetIndentParensExpression(int indent, IEnumerable<IToken> ownedTokens) {
    var itemIndent = indent + SpaceTab;
    var commaIndent = indent;

    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "[":
        case "{":
        case "(": {
            if (IsFollowedByNewline(token)) {
              SetIndentations(token, indent, indent, itemIndent);
            } else {
              SetAlign(indent, token, out itemIndent, out commaIndent);
            }

            break;
          }
        case ",": {
            SetIndentations(token, itemIndent, commaIndent, itemIndent);
            break;
          }
        case ":=": {
            SetIndentations(token, itemIndent, itemIndent, itemIndent + SpaceTab);
            break;
          }
        case "]":
        case "}":
        case ")": {
            SetIndentations(token, itemIndent, indent, indent);
            break;
          }
      }
    }

    return true;
  }

  private bool SetIndentComprehensionExpr(int indent, IEnumerable<IToken> ownedTokens) {
    var alreadyAligned = false;
    var assignIndent = indent;
    var afterAssignIndent = assignIndent + SpaceTab;

    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "forall":
        case "exists":
        case "map":
        case "set":
        case "imap":
        case "iset": {
            indent = GetNewTokenVisualIndent(token, indent);
            assignIndent = indent;
            afterAssignIndent = assignIndent + SpaceTab;
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case ":=":
        case "::": {
            if (alreadyAligned) {
              SetIndentations(token, afterAssignIndent, assignIndent, afterAssignIndent);
            } else {
              if (IsFollowedByNewline(token)) {
                SetIndentations(token, afterAssignIndent, assignIndent, afterAssignIndent);
              } else {
                alreadyAligned = true;
                SetAlign(indent, token, out afterAssignIndent, out assignIndent);
                assignIndent -= 1; // because "::" or ":=" has one more char than a comma 
              }
            }
            break;
          }
      }
    }

    return true;
  }

  private bool SetIndentCases(int indent, IEnumerable<IToken> ownedTokens, Action indentInside) {
    var matchCaseNoIndent = false;
    var caseIndent = indent;
    var afterArrowIndent = indent + SpaceTab;
    var decreasesElemIndent = indent + SpaceTab + SpaceTab;
    var commaIndent = decreasesElemIndent;
    // Need to ensure that the "case" is at least left aligned with the match/if/while keyword
    IToken decisionToken = null;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }

      switch (token.val) {
        case "if":
        case "while":
        case "match": {
            decisionToken = token;
            if (ReduceBlockiness && token.Prev.val is "=>" or ":=" or ":-" or ":|" && token.Prev.line == token.line) {
              caseIndent = GetIndentBefore(token.Prev);
              indent = caseIndent - SpaceTab;
            } else {
              caseIndent = GetNewTokenVisualIndent(token, indent);
            }

            afterArrowIndent = caseIndent + SpaceTab;
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case "{":
          caseIndent = indent + SpaceTab;
          afterArrowIndent = caseIndent + SpaceTab;
          SetDelimiterIndentedRegions(token, indent);
          break;
        case "}":
          SetClosingIndentedRegion(token, indent);
          break;
        case "case":
          if (decisionToken != null && decisionToken.line == token.line) {
            caseIndent = GetNewTokenVisualIndent(token, indent);
          }
          SetOpeningIndentedRegion(token, caseIndent);
          break;
        case "=>":
          if (token.Next.val == "{" || token.Next.val == "(") {
            // The block will already indent this
            SetIndentations(token, caseIndent, caseIndent, caseIndent);
          } else if (IsFollowedByNewline(token)) {
            SetIndentations(token, afterArrowIndent, afterArrowIndent, afterArrowIndent);
          } else {
            SetAlign(afterArrowIndent, token, out _, out _);
          }

          break;
        case ",": { // For decreases clauses
            SetIndentations(token, decreasesElemIndent, commaIndent, decreasesElemIndent);
            break;
          }
        case "decreases": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent + SpaceTab);
              decreasesElemIndent = indent + SpaceTab + SpaceTab;
              commaIndent = decreasesElemIndent;
            } else {
              SetAlign(indent + SpaceTab, token, out decreasesElemIndent, out commaIndent);
            }

            break;
          }
        case "invariant": {
            SetOpeningIndentedRegion(token, indent + SpaceTab);
            break;
          }
      }
    }

    indentInside();

    // Ensure comments just before a "case" are aligned with this case.
    foreach (var token in ownedTokens) {
      switch (token.val) {
        case "case":
          SetIndentations(token.Prev, after: caseIndent);
          break;
      }
    }

    return false;
  }

  private bool SetIndentITE(int indent, ITEExpr iteExpr) {
    var lineThen = 0;
    var colThen = 0;
    IToken thenToken = null;
    foreach (var token in iteExpr.OwnedTokens) {
      switch (token.val) {
        case "if": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent);
            } else {
              SetAlignOpen(token, indent);
            }
            Visit(iteExpr.Test, indent);
            break;
          }
        case "then": {
            lineThen = token.line;
            colThen = token.col;
            thenToken = token;
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent);
            } else {
              var rightIndent = GetRightAlignIndentAfter(token, indent);
              SetIndentations(token, indent, indent, rightIndent);
            }
            Visit(iteExpr.Thn, indent + SpaceTab);            // Override the last indentation so that comments are on the same column as "else"
            SetIndentations(token.Prev, after: indent);

            break;
          }
        case "else": {
            if (token.col == colThen) {
              // We keep the alignment.
              var newElseIndent = GetNewTokenVisualIndent(thenToken, indent);
              SetDelimiterIndentedRegions(token, newElseIndent);
            } else if (token.Next.val == "if" || token.line == lineThen) { // Don't indent the subexpression
              SetIndentations(token, before: indent, sameLineBefore: indent, after: indent);
            } else if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent);
            } else {
              SetAlign(indent, token, out _, out _);
            }

            Visit(iteExpr.Els, indent + SpaceTab);
            // Override the last indentation so that comments are on the same column as "else"
            SetIndentations(token.Prev, after: indent);
            break;
          }
      }
    }

    return false;
  }


  private bool SetIndentVarDeclStmt(int indent, IEnumerable<IToken> ownedTokens, bool noLHS, bool isLetExpr) {
    var rightIndent = indent + SpaceTab;
    var commaIndent = indent + SpaceTab;
    var afterSemicolonIndent = indent;
    var hadGhost = false;
    var assignOpIndent = noLHS ? indent : indent + SpaceTab;
    var isAmpVar = false;
    var ampVarIndent = indent;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "ghost": {
            afterSemicolonIndent = GetNewTokenVisualIndent(token, indent);
            SetOpeningIndentedRegion(token, indent);
            hadGhost = true;
            break;
          }
        case "var": {
            if (token.Prev.val == "&&" && token.Prev.line == token.line) {
              isAmpVar = true;
              ampVarIndent = GetNewTokenVisualIndent(token.Prev, indent);
            }
            if (!hadGhost) {
              afterSemicolonIndent = GetNewTokenVisualIndent(token, indent);
            }

            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent);
            } else {
              SetAlign(indent, token, out rightIndent, out commaIndent);
            }

            break;
          }
        case ",":
          SetDelimiterSpeciallyIndentedRegions(token, commaIndent, rightIndent);
          break;
        case ":|":
        case ":-":
        case ":=": {
            if (isLetExpr) {
              if (!IsFollowedByNewline(token)) {
                SetAlign(assignOpIndent, token, out rightIndent, out commaIndent);
              } else {
                SetIndentations(token, assignOpIndent, assignOpIndent, indent + SpaceTab);
                commaIndent = indent + SpaceTab;
                rightIndent = indent + SpaceTab;
              }
            } else {
              // For variable declarations, :=, :| and :- is part of the UpdateStmt
            }
            break;
          }
        case ";":
          SetIndentations(token, afterSemicolonIndent + SpaceTab,
            afterSemicolonIndent + SpaceTab,
            isAmpVar ? ampVarIndent :
            afterSemicolonIndent);
          break;
          // Otherwise, these are identifiers, We don't need to specify their indentation.
      }
    }

    return true;
  }

  private bool SetIndentLabelTokens(IToken token, int indent) {
    if (token.val == "label") {
      SetOpeningIndentedRegion(token, indent);
    } else if (token.val == ":" && token.Prev.Prev.val == "label") {
      SetClosingIndentedRegion(token, indent);
    } else if (token.Prev.val != "label") {
      return false;
    }

    return true;
  }

  private void SetIndentLikeLoop(IEnumerable<IToken> ownedTokens, Statement body, int indent) {
    var decreasesElemIndent = indent + SpaceTab;
    var commaIndent = indent + SpaceTab;
    var first = true;
    foreach (var token in ownedTokens) {
      if (first) {
        SetOpeningIndentedRegion(token, indent);
        first = false;
      }
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "while":
        case "forall": {
            SetOpeningIndentedRegion(token, indent);
            break;
          }
        case ",": { // For decreases clauses
            SetIndentations(token, decreasesElemIndent, commaIndent, decreasesElemIndent);
            break;
          }
        case "decreases": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent + SpaceTab);
              decreasesElemIndent = indent + SpaceTab + SpaceTab;
              commaIndent = decreasesElemIndent;
            } else {
              SetAlign(indent + SpaceTab, token, out decreasesElemIndent, out commaIndent);
            }

            break;
          }
        case "...": {
            SetDelimiterInsideIndentedRegions(token, indent);
            break;
          }
        case "ensures":
        case "invariant": {
            if (IsFollowedByNewline(token)) {
              SetOpeningIndentedRegion(token, indent + SpaceTab);
            } else {
              SetAlign(indent + SpaceTab, token, out _, out _);
            }
            break;
          }
      }
    }

    if (body != null) {
      SetDelimiterIndentedRegions(body.Tok, indent);
      if (body.EndTok.val == "}") {
        SetClosingIndentedRegion(body.EndTok, indent);
      }

      Visit(body, indent);
    }
  }

  private bool SetChainingExprIndent(int indent, ChainingExpression chainingExpression) {
    // Chaining expressions try to align their values if possible
    var itemIndent = GetNewTokenVisualIndent(chainingExpression.Operands[0].StartToken, indent);

    foreach (var token in chainingExpression.OwnedTokens) {
      switch (token.val) {
        case "[":
          break;
        case "#":
          break;
        case "]":
          break;
        default:
          SetIndentations(token, itemIndent, Math.Max(itemIndent - token.val.Length - 1, 0), itemIndent);
          break;
      }
    }

    return true;
  }

  private bool SetBinaryExprIndent(int indent, BinaryExpr binaryExpr) {
    if (binaryExpr.Op is BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or) {
      var ownedTokens = binaryExpr.OwnedTokens.ToList();
      // Alignment required.
      if (ownedTokens.Count == 2) {
        var firstToken = ownedTokens[0];
        var secondToken = ownedTokens[1];
        indent = GetNewTokenVisualIndent(firstToken, GetIndentBefore(firstToken));
        var c = 0;
        while (c < firstToken.TrailingTrivia.Length && firstToken.TrailingTrivia[c] == ' ') {
          c++;
        }

        var conjunctExtraIndent = c + SpaceTab;
        binOpIndent = indent;
        binOpArgIndent = indent + conjunctExtraIndent;
        SetIndentations(firstToken, binOpIndent, binOpIndent, binOpArgIndent);
        SetIndentations(secondToken, binOpIndent, binOpIndent, binOpArgIndent);
      } else if (ownedTokens.Count > 0) {
        if (ownedTokens[0].val == "requires") { // Requirement conjunctions inside lambdas are separated by the keyword "requires"
          if (binaryExpr.StartToken.Prev.val == "requires") {
            binOpIndent = GetIndentBefore(binaryExpr.StartToken.Prev);
          }
        }
        if (binOpIndent > 0) {
          SetIndentations(ownedTokens[0], binOpIndent, binOpIndent, binOpArgIndent);
        } else {
          var startToken = binaryExpr.StartToken;
          var newIndent = GetNewTokenVisualIndent(startToken, GetIndentBefore(startToken));
          SetIndentations(ownedTokens[0], newIndent, newIndent, newIndent);
        }
      }

      if (binOpIndent > 0 && (binaryExpr.E0 is not BinaryExpr { Op: var op } || op != binaryExpr.Op)) {
        binOpIndent = -1;
        binOpArgIndent = -1;
      }

      return true; // Default indentation
    } else if (binaryExpr.Op is BinaryExpr.Opcode.Imp or BinaryExpr.Opcode.Exp) {
      foreach (var token in binaryExpr.OwnedTokens) {
        switch (token.val) {
          case "==>": {
              SetOpeningIndentedRegion(token, indent);
              break;
            }
          case "<==": {
              SetIndentations(token, indent, indent, indent);
              break;
            }
        }
      }
      Visit(binaryExpr.E0, indent);
      Visit(binaryExpr.E1, binaryExpr.Op is BinaryExpr.Opcode.Exp ? indent : indent + SpaceTab);
      SetIndentations(binaryExpr.EndToken, after: indent);
      return false;
    } else if (binaryExpr.Op is BinaryExpr.Opcode.Eq or BinaryExpr.Opcode.Le or BinaryExpr.Opcode.Lt or BinaryExpr.Opcode.Ge or BinaryExpr.Opcode.Gt or BinaryExpr.Opcode.Iff or BinaryExpr.Opcode.Neq) {
      var itemIndent = GetNewTokenVisualIndent(
        binaryExpr.E0.EndToken.line != binaryExpr.E1.StartToken.line ?
          binaryExpr.E0.StartToken :
          binaryExpr.E1.StartToken, indent);
      var startToken = binaryExpr.E0.StartToken;
      if (startToken.Prev.line == startToken.line) {
        // like assert E0
        //          == E1
        // Careful: The binaryExpr.op's first column should be greater than the
        // token's first column before E0.StartToken. 
        foreach (var token in binaryExpr.OwnedTokens) {
          switch (token.val) {
            case "==":
            case "<=":
            case "<":
            case ">=":
            case ">":
            case "<==>":
            case "!=": {
                var selfIndent = IsFollowedByNewline(token) ? itemIndent : Math.Max(itemIndent - token.val.Length - 1, 0);
                if (GetNewTokenVisualIndent(startToken.Prev, itemIndent) < selfIndent) {
                  SetIndentations(token, itemIndent, selfIndent, itemIndent);
                }

                break;
              }
          }
        }
      }
      Visit(binaryExpr.E0, itemIndent);
      Visit(binaryExpr.E1, itemIndent);
      SetIndentations(binaryExpr.EndToken, after: indent);
      return false;
    } else {
      foreach (var token in binaryExpr.OwnedTokens) {
        SetIndentations(token, indent, indent, indent);
      }
      Visit(binaryExpr.E0, indent);
      Visit(binaryExpr.E1, indent);
      SetIndentations(binaryExpr.EndToken, after: indent);
      return false;
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
    commaIndent = GetNewTokenVisualIndent(token, indent) + token.val.Length - 1;
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
  private void SetAlignOpen(IToken token, int indent) {
    var rightIndent = GetRightAlignIndentAfter(token, indent);
    SetIndentations(token, indent, indent, rightIndent);
  }
  #endregion

  public string ReindentLeadingTrivia(IToken token, bool precededByNewline,
    string indentationBefore, string lastIndentation) {
    return Reindent(token, false, precededByNewline, indentationBefore, lastIndentation);
  }

  public string ReindentTrailingTrivia(IToken token, bool precededByNewline,
    string indentationBefore, string lastIndentation) {
    return Reindent(token, true, precededByNewline, indentationBefore, lastIndentation);
  }

  #region Override for implementing IIndentationFormatter
  /// Given a space around a token (input),
  /// * precededByNewline means it's a leading space that was preceded by a newline
  /// or a trailing (isLeadingSpace==false)
  /// changes the indentation so that on the lines before, it uses indentationBefore,
  /// and on the last line it uses lastIndentation
  /// If it's a trailing space, no indentation is added after the last \n because it would be handled by the next leading space.
  /// 
  /// This function implements IIndentationFormatter.Reindent and is called by Formatter.dfy
  public string Reindent(IToken token, bool trailingTrivia, bool precededByNewline, string indentationBefore, string lastIndentation) {
    var input = trailingTrivia ? token.TrailingTrivia : token.LeadingTrivia;
    var commentExtra = "";
    // Invariant: Relative indentation inside a multi-line comment should be unchanged
    var originalCommentIndent = 0;
    var newCommentIndent = 0;
    var previousMatchWasSingleLineCommentToAlign = false;

    // Apply the given rules on a match of a (newline|beginning) + space + comment?
    string ApplyIndentRules(System.Text.RegularExpressions.Match match) {
      if (match.Groups["trailingWhitespace"].Success) {
        return HelperString.RemoveTrailingWhitespace ? "" : match.Groups["trailingWhitespace"].Value;
      }

      var startOfString = match.Groups["previousChar"].Value == "";
      var commentType = match.Groups["commentType"].Value;
      if (startOfString && !precededByNewline) {
        if (commentType.StartsWith("//")) {
          // Possibly align consecutive // trailing comments
          if (originalCommentIndent == 0) {
            originalCommentIndent = token.col - 1 + token.val.Length + match.Groups["currentIndent"].Value.Length;
            newCommentIndent = GetNewTokenVisualIndent(token, 0) + token.val.Length + match.Groups["currentIndent"].Value.Length;
            previousMatchWasSingleLineCommentToAlign = true;
          }
        }

        if (HelperString.RemoveTrailingWhitespace && commentType.StartsWith("\r") || commentType.StartsWith("\n")) {
          precededByNewline = true;
          return commentType;
        }

        if (!commentType.StartsWith("/*")) {
          return match.Groups[0].Value;
        }
      }

      if (commentType.Length == 0) {
        //End of the string. Do we indent or not?
        return precededByNewline && !trailingTrivia ? lastIndentation :
          trailingTrivia ? "" : // The leading trivia of the next token is going to take care of the indentation
          match.Groups[0].Value;
      }

      if (!startOfString) {
        precededByNewline = true;
      }

      if (commentType.StartsWith("/*")) {
        var doubleStar = commentType.StartsWith("/**") && !commentType.StartsWith("/***");
        var originalComment = match.Groups["commentType"].Value;

        var absoluteOriginalIndent = match.Groups["currentIndent"].Length;
        var newAbsoluteIndent = indentationBefore.Length;
        if (!precededByNewline) {
          // It has to be the trailing trivia of that token.
          absoluteOriginalIndent = token.col - 1 + token.val.Length + absoluteOriginalIndent;
          newAbsoluteIndent = GetNewTokenVisualIndent(token, indentationBefore.Length) + token.val.Length + match.Groups["currentIndent"].Length;
        }

        var relativeIndent = newAbsoluteIndent - absoluteOriginalIndent;
        var initialRelativeIndent = relativeIndent;
        var tryAgain = true;
        string result = "";
        // This loop executes at most two time. The second time is necessary only if the indentation before the first /* decreases
        // and there were items that would have been moved into a negative column.
        // e.g.
        //
        // const x := 2;
        //     /* Start of comment
        //   end of comment */
        //
        // would be, after the first iteration
        //
        // const x := 2;
        // /* Start of comment
        // end of comment */
        //
        // which breaks the alignment. So with `tryAgain`, it  corrects the offset so that the comment becomes:
        //
        // const x := 2;
        //   /* Start of comment
        // end of comment */
        //
        while (tryAgain)
        // decreases newAbsoluteIndent - relativeIndent
        {
          var canIndentLinesStartingWithStar = true;
          tryAgain = false;
          result = new Regex($@"(?<=\r?\n|\r(?!\n))(?<existingIndent>[ \t]*)(?<star>\*)?").Replace(originalComment, match1 => {
            if (canIndentLinesStartingWithStar && match1.Groups["star"].Success) {
              return indentationBefore + (doubleStar ? "  *" : " *");
            }

            canIndentLinesStartingWithStar = false;
            // Reindent in block:
            var newIndent = match1.Groups["existingIndent"].Value.Length + relativeIndent;
            if (newIndent < 0) {
              relativeIndent -= newIndent;
              tryAgain = true;
              newIndent = 0;
            }

            return new string(' ', newIndent) + (match1.Groups["star"].Success ? match1.Groups["star"].Value : "");
          });
        }

        previousMatchWasSingleLineCommentToAlign = false;
        if (precededByNewline) {
          return new string(' ', absoluteOriginalIndent + relativeIndent) + result;
        }

        return new string(' ', match.Groups["currentIndent"].Length + relativeIndent - initialRelativeIndent) + result;
      }

      if (commentType.StartsWith("//")) {
        if (commentType.StartsWith("///") && !commentType.StartsWith("////")) {
          // No indentation
          return match.Groups["commentType"].Value;
        }

        if (previousMatchWasSingleLineCommentToAlign) {
          if (originalCommentIndent == match.Groups["currentIndent"].Value.Length) {
            return new string(' ', newCommentIndent) + match.Groups["commentType"].Value;
          }
        }

        var referenceToken = token.Next;
        if (match.Groups["caseCommented"].Success && token.Next != null && (token.Next.val == match.Groups["caseCommented"].Value || FirstTokenOnLineIs(token, t => {
          referenceToken = t;
          return t.val == match.Groups["caseCommented"].Value;
        }))) {
          indentationBefore = new string(' ', GetNewTokenVisualIndent(referenceToken, indentationBefore.Length));
        }

        previousMatchWasSingleLineCommentToAlign = false;

        return indentationBefore + match.Groups["commentType"].Value;
      }

      if (commentType.StartsWith("\r") || commentType.StartsWith("\n")) {
        previousMatchWasSingleLineCommentToAlign = false;
        return (HelperString.BlankNewlinesWithoutSpaces ? "" : indentationBefore) + match.Groups["commentType"].Value;
      }

      previousMatchWasSingleLineCommentToAlign = false;

      // Last line
      return lastIndentation;
    }

    return HelperString.NewlineRegex.Replace(input, ApplyIndentRules);
  }

  private static readonly Dictionary<int, string> indentationsCache = new();

  private static string IndentationBy(int characters) {
    return indentationsCache.GetOrCreate(characters, () => new string(' ', characters));
  }

  public void GetIndentation(IToken token, string currentIndentation,
      out string indentationBefore,
      out string lastIndentation,
      out string indentationAfter) {
    if (token.kind == 0) {
      currentIndentation = "";
    }
    indentationBefore = currentIndentation;
    lastIndentation = currentIndentation;
    indentationAfter = currentIndentation;
    if (posToIndentBefore.TryGetValue(token.pos, out var preIndentation)) {
      indentationBefore = IndentationBy(preIndentation);
      lastIndentation = indentationBefore;
      indentationAfter = indentationBefore;
    }
    if (posToIndentLineBefore.TryGetValue(token.pos, out var sameLineIndentation)) {
      lastIndentation = IndentationBy(sameLineIndentation);
      indentationAfter = lastIndentation;
    }
    if (posToIndentAfter.TryGetValue(token.pos, out var postIndentation)) {
      indentationAfter = IndentationBy(postIndentation);
    }
  }

  public void GetNewLeadingTrailingTrivia(IToken token, string currentIndent, bool previousTrailingTriviaEndedWithNewline,
    out string newLeadingTrivia, out string newTrailingTrivia, out string newIndentation,
    out bool nextLeadingTriviaWillBePrecededByNewline) {
    _Companion_IIndentationFormatter.GetNewLeadingTrailingTrivia(this, token, currentIndent,
      previousTrailingTriviaEndedWithNewline, out newLeadingTrivia, out newTrailingTrivia, out newIndentation,
      out nextLeadingTriviaWillBePrecededByNewline);
  }

  #endregion
}


public static class HelperString {
  // If we ever decide that blank lines should keep spaces, we can set this to false. 
  public static bool BlankNewlinesWithoutSpaces = true;

  // If we remove whitespace (tabs or space) at the end of lines. 
  public static bool RemoveTrailingWhitespace = true;

  // A regex that checks if a particular string ends with a newline and some spaces.
  private static readonly Regex EndsWithNewlineRegex =
    new(@"(\r?\n|\r)[ \t]*$");

  // This is used by Formatter.dfy
  public static bool EndsWithNewline(string s) {
    return EndsWithNewlineRegex.IsMatch(s);
  }

  private static readonly string NoCommentDelimiter = @"(?:(?!/\*|\*/)[\s\S])*";

  private static readonly string MultilineCommentContent =
    $@"(?:{NoCommentDelimiter}(?:(?'Open'/\*)|(?'-Open'\*/)))*{NoCommentDelimiter}";

  public static readonly Regex NewlineRegex =
    new($@"(?<=(?<previousChar>\r?\n|\r(?!\n)|^))(?<currentIndent>[ \t]*)(?<commentType>/\*{MultilineCommentContent}\*/|///?/? ?(?<caseCommented>(?:\||case))?|\r?\n|\r(?!\n)|$)|(?<=\S|^)(?<trailingWhitespace>[ \t]+)(?=\r?\n|\r(?!\n))");
}
