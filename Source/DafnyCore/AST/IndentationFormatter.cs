using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Formatting;

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
public class IndentationFormatter : TopDownVisitor<int>, IIndentationFormatter {

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

  public readonly int SpaceTab = 2;

  private readonly Dictionary<int, int> posToIndentBefore = new();
  private readonly Dictionary<int, int> posToIndentLineBefore = new();
  private readonly Dictionary<int, int> posToIndentAfter = new();

  // Used for bullet points && and ||
  public int binOpIndent = -1;
  public int binOpArgIndent = -1;


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
    foreach (var child in program.DefaultModuleDef.ConcreteChildren) {
      if (child is TopLevelDecl topLevelDecl) {
        indentationFormatter.SetDeclIndentation(topLevelDecl, 0);
      } else if (child is Include include) {
        if (include.OwnedTokens.Any()) {
          indentationFormatter.SetOpeningIndentedRegion(include.OwnedTokens.First(), 0);
        }
      }
    }

    return indentationFormatter;
  }

  public IEnumerable<Expression> SubExpressions(Expression expr) {
    return expr is ConcreteSyntaxExpression concreteSyntaxExpression
      ? concreteSyntaxExpression.PreResolveSubExpressions
      : expr.SubExpressions;
  }


  protected override bool VisitOneExpr(Expression expr, ref int unusedIndent) {
    if (expr == null) {
      return false;
    }
    var firstToken = expr.StartToken;
    var indentBefore = GetIndentBefore(firstToken);
    if (expr is ICanFormat canFormatNode) {
      return canFormatNode.SetIndent(indentBefore, this);
    }

    return true;
  }

  protected override bool VisitOneStmt(Statement stmt, ref int unusedIndent) {
    if (stmt == null) {
      return false;
    }
    var firstToken = stmt.StartToken;
    var indentBefore = GetIndentBefore(firstToken);
    if (stmt is ICanFormat canFormatNode) {
      return canFormatNode.SetIndent(indentBefore, this);
    }
    // Best heuristic for new elements is to indent them using the method's formatting
    SetMethodLikeIndent(stmt.Tok, stmt.OwnedTokens, indentBefore);
    SetIndentations(stmt.EndToken, -1, -1, indentBefore);

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

  public int GetIndentBefore(IToken token) {
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

  public int GetNewTokenVisualIndent(IToken token, int defaultIndent) {
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
  public int GetRightAlignIndentAfter(IToken token, int indentFallback) {
    var trailingSpace = GetTrailingSpace(token);
    return GetNewTokenVisualIndent(token, indentFallback) + token.val.Length + trailingSpace;
  }

  private static readonly Regex FollowedByNewlineRegex = new Regex("^[ \t]*([\r\n]|//)");

  public static bool IsFollowedByNewline(IToken token) {
    return FollowedByNewlineRegex.IsMatch(token.TrailingTrivia);
  }

  #endregion

  #region All SetIndent* methods

  // 'before' is the hypothetical indentation of a comment before that token, and of the previous token if it does not have a set indentation
  // 'sameLineBefore' is the hypothetical indentation of this token if it was on its own line
  // 'after' is the hypothetical indentation of a comment after that token, and of the next token if it does not have a set indentation
  public void SetIndentations(IToken token, int before = -1, int sameLineBefore = -1, int after = -1) {
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
              // In the future, we might want to use this if reducing blockiness as well
              // However, it has some undesirable side-effects which would need to be fixed
              SetOpeningIndentedRegion(token, indent2);
            } else {
              SetAlign(indent2, token, out rightIndent, out commaIndent);
            }

            commaIndent = indent2;
            break;
          }
      }
    }
  }

  public void SetTypeIndentation(Type type) {
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

  // ReSharper disable once UnusedParameter.Local
  void SetAttributeIndentation(Attributes attributes) {
    // If we ever need multiline attributes, here is the place to format them appropriatedly
  }

  public void SetDecreasesExpressionIndentation(Expression expression, int indent) {
    SetExpressionIndentation(expression);
    SetIndentations(expression.EndToken, after: indent);
  }

  public void SetAttributedExpressionIndentation(AttributedExpression attrExpression, int indent) {
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
      SetClosingIndentedRegion(byMethodBody.EndToken, indent);
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
            if (token.line != token.Next.line) {
              extraIndent = classToken != null && classToken.line == token.line ? 0 : SpaceTab;
              commaIndent += extraIndent;
              SetIndentations(token, after: indent + SpaceTab + extraIndent);
            } else {
              extraIndent += 2;
              commaIndent = indent + SpaceTab;
              SetIndentations(token, after: indent + SpaceTab);
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
    if (moduleDecl.OwnedTokens.FirstOrDefault() is { } theToken) {
      SetOpeningIndentedRegion(theToken, indent);
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
    var innerIndent = SetModuleDeclIndent(moduleDecl.ModuleDef.OwnedTokens, indent);
    foreach (var decl2 in moduleDecl.ModuleDef.TopLevelDecls) {
      SetDeclIndentation(decl2, innerIndent);
    }
    foreach (var decl2 in moduleDecl.ModuleDef.PrefixNamedModules) {
      SetDeclIndentation(decl2.Item2, innerIndent);
    }
  }

  private int SetModuleDeclIndent(IEnumerable<IToken> ownedTokens, int indent) {
    var innerIndent = indent + SpaceTab;
    var allTokens = ownedTokens.ToList();
    if (allTokens.Any()) {
      SetOpeningIndentedRegion(allTokens[0], indent);
    }
    foreach (var token in allTokens) {
      switch (token.val) {
        case "abstract":
        case "module": {
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

    var ownedTokens = datatypeDecl.OwnedTokens.Concat(datatypeDecl.Ctors.SelectMany(ctor => ctor.OwnedTokens))
      .OrderBy(token => token.pos);
    foreach (var token in ownedTokens) {
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

  private bool SetIndentModifyStatement(ModifyStmt stmt, int indentBefore) {
    var ownedTokens = stmt.OwnedTokens;
    var commaIndent = indentBefore + SpaceTab;
    var afterCommaIndent = commaIndent;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indentBefore)) {
        continue;
      }
      switch (token.val) {
        case "modifies":
        case "modify":
          if (IsFollowedByNewline(token)) {
            SetOpeningIndentedRegion(token, indentBefore);
          } else {
            SetAlign(indentBefore, token, out afterCommaIndent, out commaIndent);
          }
          break;
        case ",":
          SetIndentations(token, afterCommaIndent, commaIndent, afterCommaIndent);
          break;
        case "{":
          SetOpeningIndentedRegion(token, indentBefore);
          break;
        case "}":
        case ";":
          SetClosingIndentedRegion(token, indentBefore);
          break;
      }
    }

    if (stmt.Body != null && stmt.Body.StartToken.line > 0) {
      SetOpeningIndentedRegion(stmt.Body.StartToken, indentBefore);
    }

    return true;
  }

  public bool SetIndentAssertLikeStatement(Statement stmt, int indent) {
    var ownedTokens = stmt.OwnedTokens;
    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, indent)) {
        continue;
      }
      switch (token.val) {
        case "assume":
        case "expect":
        case "assert":
        case "yield":
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

  public void SetIndentBody(Statement body, int indent) {
    if (body == null) {
      return;
    }
    SetDelimiterIndentedRegions(body.StartToken, indent);
    SetClosingIndentedRegion(body.EndToken, indent);
    Visit(body, indent);
  }

  public bool SetIndentPrintRevealStmt(int indent, IEnumerable<IToken> ownedTokens) {
    var commaIndent = indent + SpaceTab;
    var innerIndent = indent + SpaceTab;
    var afterSemicolonIndent = indent;
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
          afterSemicolonIndent = GetNewTokenVisualIndent(token, indent);

          break;
        case ",":
          SetIndentations(token, innerIndent, commaIndent, innerIndent);
          break;
        case ";":
          SetClosingIndentedRegionInside(token, afterSemicolonIndent);
          break;
      }
    }

    return true;
  }

  public bool SetIndentUpdateStmt(ConcreteUpdateStatement stmt, int indent, bool inner) {
    var ownedTokens = stmt.OwnedTokens.ToList();
    var opIndentDefault =
      stmt is AssignOrReturnStmt assignStmt && assignStmt.Lhss.Count == 0
        ? indent : indent + SpaceTab;
    var startToken = stmt.StartToken;
    int startAssignmentIndent = inner ? indent + SpaceTab : indent;
    int afterStartIndent = indent + SpaceTab;
    var rightIndent = indent + SpaceTab;
    var commaIndent = indent + SpaceTab;
    SetIndentations(startToken, startAssignmentIndent, startAssignmentIndent, afterStartIndent);

    var rhss = stmt is UpdateStmt updateStmt ? updateStmt.Rhss
      : stmt is AssignOrReturnStmt assignOrReturnStmt ?
        new List<AssignmentRhs> { assignOrReturnStmt.Rhs }.Concat(assignOrReturnStmt.Rhss).ToList()
        : new List<AssignmentRhs>();

    // For single Rhs that are of the form [new] X(args....),
    // we can even further decrease the indent so that the last parenthesis
    // is aligned with the beginning of the declaration. 
    var firstRhsOneSingleLine = rhss.Count >= 1 && rhss[0].StartToken.line == rhss[0].EndToken.line;
    var assignmentOperator = ownedTokens.Find(token => token.val == ":=" || token.val == ":-" || token.val == ":|");
    if (assignmentOperator == null) {
      rightIndent = startAssignmentIndent;
    }

    void InferRightIndentFromRhs() {
      if (!rhss.Any()) {
        return;
      }

      var rhs = rhss[0];
      if (ReduceBlockiness) {
        rightIndent = indent;
        return;
      }

      rightIndent = GetNewTokenVisualIndent(rhs.RangeToken.StartToken, rightIndent);
    }

    if (!ownedTokens.Any(token => token.val == ":=" || token.val == ":-" || token.val == ":|")) {
      InferRightIndentFromRhs();
    }

    foreach (var token in ownedTokens) {
      if (SetIndentLabelTokens(token, startAssignmentIndent)) {
        continue;
      }
      switch (token.val) {
        case ",":
          SetDelimiterSpeciallyIndentedRegions(token, commaIndent, rightIndent);
          break;
        case ":|":
        case ":-":
        case ":=": {
            if (!IsFollowedByNewline(assignmentOperator)) {
              if (ReduceBlockiness && !firstRhsOneSingleLine) {
                if (rhss.Count == 1 && rhss[0] is not ExprRhs { Expr: LambdaExpr }) {
                  rightIndent = indent;
                  commaIndent = indent;
                } else {
                  rightIndent = indent + SpaceTab;
                  commaIndent = indent = SpaceTab;
                }
                SetIndentations(assignmentOperator, afterStartIndent, opIndentDefault, rightIndent);
              } else {
                SetAlign(opIndentDefault, assignmentOperator, out rightIndent, out commaIndent);
              }
            } else {
              rightIndent = afterStartIndent;
              SetIndentations(assignmentOperator, afterStartIndent, opIndentDefault, rightIndent);
            }
            break;
          }

        case ";":
          SetClosingIndentedRegionInside(token, indent);
          break;
          // Otherwise, these are identifiers, We don't need to specify their indentation.
      }
    }

    foreach (var rhs in rhss) {
      if (rhs.OwnedTokens.Any(token => token.val == "(")) {
        SetIndentParensExpression(rightIndent, rhs.OwnedTokens);
      }

      foreach (var node in rhs.PreResolveSubExpressions) {
        Visit(node, rightIndent);
      }
    }

    return false;
  }

  public void VisitAlternatives(List<GuardedAlternative> alternatives, int indent) {
    foreach (var alternative in alternatives) {
      Visit(alternative.Guard, indent + SpaceTab);
      foreach (var bodyStmt in alternative.Body) {
        Visit(bodyStmt, indent + SpaceTab);
      }
    }
  }

  public bool SetIndentParensExpression(int indent, IEnumerable<IToken> ownedTokens) {
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
            SetIndentations(token, itemIndent, itemIndent,
                IsFollowedByNewline(token) ?
                itemIndent + SpaceTab : itemIndent);

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

  public bool SetIndentCases(int indent, IEnumerable<IToken> ownedTokens, Action indentInside) {
    var matchCaseNoIndent = false;
    var caseIndent = indent;
    var afterArrowIndent = indent + SpaceTab;
    var decreasesElemIndent = indent + SpaceTab + SpaceTab;
    var commaIndent = decreasesElemIndent;
    // Need to ensure that the "case" is at least left aligned with the match/if/while keyword
    IToken decisionToken = null;
    var allTokens = ownedTokens as IToken[] ?? ownedTokens.ToArray();
    foreach (var token in allTokens) {
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
          if (!IsFollowedByNewline(token)) {
            if (ReduceBlockiness) {
              SetIndentations(token, afterArrowIndent, afterArrowIndent, caseIndent);
            } else {
              SetAlign(afterArrowIndent, token, out _, out _);
            }
          } else {
            SetIndentations(token, afterArrowIndent, afterArrowIndent, afterArrowIndent);
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
    foreach (var token in allTokens) {
      switch (token.val) {
        case "case":
          SetIndentations(token.Prev, after: caseIndent);
          break;
      }
    }

    return false;
  }

  public bool SetIndentVarDeclStmt(int indent, IEnumerable<IToken> ownedTokens, bool noLHS, bool isLetExpr) {
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

  public bool SetIndentLabelTokens(IToken token, int indent) {
    if (token.val == "label") {
      SetOpeningIndentedRegion(token, indent);
    } else if (token.val == ":" && token.Prev.Prev.val == "label") {
      SetClosingIndentedRegion(token, indent);
    } else if (token.Prev.val != "label") {
      return false;
    }

    return true;
  }

  public void SetIndentLikeLoop(IEnumerable<IToken> ownedTokens, Statement body, int indent) {
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
      if (body.EndToken.val == "}") {
        SetClosingIndentedRegion(body.EndToken, indent);
      }

      Visit(body, indent);
    }
  }

  public bool TryGetIndentBefore(IToken token, out int indent) {
    return posToIndentBefore.TryGetValue(token.pos, out indent);
  }
  public bool TryGetIndentLineBefore(IToken token, out int indent) {
    return posToIndentLineBefore.TryGetValue(token.pos, out indent);
  }

  /// For example, the "if" keyword in the context of a statement
  ///
  /// // Not indented
  /// if       // line not indented
  ///   x == 2 // Line indented
  public void SetOpeningIndentedRegion(IToken token, int indent) {
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
  public void SetDelimiterIndentedRegions(IToken token, int indent) {
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
  public void SetDelimiterInsideIndentedRegions(IToken token, int indent) {
    SetIndentations(token, indent + SpaceTab, indent + SpaceTab, indent + SpaceTab);
  }

  // For example, a closing brace
  //
  // var x: map<   T
  //           ,
  //               U
  //               // beforeIndent
  //           >   // this line indent's
  //           //  after liene indent
  // // not indented
  private void SetClosingIndentedRegionAligned(IToken token, int beforeIndent, int indent) {
    SetIndentations(token, beforeIndent, indent, indent);
  }

  /// For example, a closing brace
  ///
  /// if true {
  ///   // indented
  /// } // not indented
  /// // not indented
  public void SetClosingIndentedRegion(IToken token, int indent) {
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
  public void SetKeywordWithoutSurroundingIndentation(IToken token, int indent) {
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
  public void SetAlign(int indent, IToken token, out int rightIndent, out int commaIndent) {
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
  public void SetAlignOpen(IToken token, int indent) {
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
  /// This method implements IIndentationFormatter.Reindent and is called by Formatter.dfy
  /// It considers the space (trivia) before a token (if trailingTrivia == false)
  /// or the space after a token (if trailingTrivia == true)
  /// and add or remove spaces after every newline to adjust the indentation.
  ///
  /// It uses indentationBefore to fix the indentation everywhere, except if
  /// the space is a leading trivia (trailingTrivia == false)
  /// and it's the last consecutive space without newlines before the token,
  /// in which case it uses lastIndentation
  ///
  /// Options:
  /// * If precededByNewline == true, it means that it's possible
  /// to add/remove spaces at the beginning of the string. Used only for leading trivia.
  /// * if trailingTrivia == true, then no indentation is added after
  ///   the eventual last newline  `\n`. Instead, when formatting the leading trivia.
  ///   of the next token, precededByNewline will be set to true.
  ///
  /// # Example
  /// 
  /// For example, consider the consecutive tokens ')' and 'const' in the following unformatted code,
  /// as well as the token 'b' and the final token '}' 
  ///
  /// ```
  /// module X {
  /// datatype A =
  ///     C()
  ///   // Comment
  ///         // continued
  ///
  ///       // Comment here
  ///  const b := 1
  ///
  /// // One last word
  ///   }
  /// ```
  ///
  /// 1. The trailing trivia of the token `)` is
  /// "\n  // Comment\n        // continued\n\n"
  ///
  /// That trivia will be processed with the options
  /// * trailingTrivia == true
  /// * precededByNewline == false (irrelevant, a trailing trivia is preceded by a token)
  /// * indentationBefore == "    " (4 spaces)
  /// * lastIndentation == "    " (irrelevant)
  /// The method will return:
  /// "\n    // Comment\n    // continued\n\n"
  ///
  /// 2. The leading trivia of the token `const` is
  /// "      // Comment here\n "
  /// That trivia will be processed with the options
  /// * trailingTrivia == false
  /// * precededByNewline == true
  /// * indentationBefore == "  " (2 spaces, it's indentation for any comment before the constant)
  /// * lastIndentation == "  " (2 spaces, it's the indentation in front of the "const" token if it's on its own line)
  /// The method will return:
  /// "  // Comment here\n  "
  ///
  /// 3. The leading trivia of the token `b``is
  /// " "
  /// That trivia will be processed with the options
  /// * trailingTrivia == false
  /// * precededByNewline == false
  /// * indentationBefore == "    "
  /// * lastIndentation == "    "
  /// However, because there are no newlines and it's not preceded
  /// by a newline, the method will return the same:
  /// " "
  /// 
  /// 4. The leading trivia of the token `}` is
  /// "// One last word\n"
  /// That trivia will be processed with the options
  /// * trailingTrivia == false
  /// * precededByNewline == true
  /// * indentationBefore == "  "
  /// * lastIndentation == ""
  /// This is an example where a comment before this token should not
  /// be aligned with that token, the method will return:
  /// "  // One last word\n"
  ///
  /// After all these formattings, the final result will be the expected one
  /// ```
  /// module X {
  ///   datatype A =
  ///     C()
  ///     // Comment
  ///     // continued
  ///
  ///   // Comment here
  ///   const b := 1
  ///
  ///   // One last word
  /// }
  /// ```
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
