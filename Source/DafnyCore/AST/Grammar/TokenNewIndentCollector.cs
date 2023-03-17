using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

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
 * Because the token printer will traverse the tokens in order, the indentation 1. is used only
 * for the trivia associated to the token in the leading whitespace of that token,
 * like `/* Comment about X * /` in the following example, which is in the leading
 * trivia of `const`
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
public class TokenNewIndentCollector : TopDownVisitor<int> {
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

  private class Indentations {
    public int Above = -1;
    public int Inline = -1;
    public int Below = -1;
  }

  private readonly Dictionary<int, Indentations> posToIndentations = new();

  private Indentations PosToIndentations(int pos) {
    return posToIndentations.GetOrCreate(pos, () => new Indentations());
  }

  // Used for bullet points && and ||
  public int binOpIndent = -1;
  public int binOpArgIndent = -1;


  internal TokenNewIndentCollector() {
    preResolve = true;
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
    var indentBefore = GetIndentInlineOrAbove(firstToken);
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
    var indentBefore = GetIndentInlineOrAbove(firstToken);
    if (stmt is ICanFormat canFormatNode) {
      return canFormatNode.SetIndent(indentBefore, this);
    }

    // Best heuristic for new elements is to indent them using the method's formatting
    SetMethodLikeIndent(stmt.Tok, stmt.OwnedTokens, indentBefore);
    SetIndentations(stmt.EndToken, -1, -1, indentBefore);

    return true;
  }

  /// If the first token on the line of the given token satisfies the given predicate.
  /// Used to detect commented cases or datatype constructors
  public static bool FirstTokenOnLineIs(IToken token, Func<IToken, bool> predicate) {
    if (token.Prev == null || token.Prev.line != token.line) {
      return predicate(token);
    }

    return FirstTokenOnLineIs(token.Prev, predicate);
  }

  // Given a token, finds the indentation that was expected before it.
  // Used for frame expressions to initially copy the indentation of "reads", "requires", etc.

  public int GetIndentAbove(IToken token) {
    if (PosToIndentations(token.pos).Above is var aboveIndentation and not -1) {
      return aboveIndentation;
    }

    return GetIndentBelowOrInlineOrAbove(token.Prev);
  }

  public int GetIndentInlineOrAbove(IToken token) {
    if (PosToIndentations(token.pos).Inline is var indentation and not -1) {
      return indentation;
    }

    return GetIndentAbove(token);
  }

  public int GetIndentBelowOrInlineOrAbove(IToken token) {
    if (token == null || token == Token.NoToken) {
      return 0;
    }

    if (PosToIndentations(token.pos).Below is var indentation and not -1) {
      return indentation;
    }

    return GetIndentInlineOrAbove(token);
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

      if (PosToIndentations(token.pos).Inline is var indentation and not -1) {
        return indentation;
      }

      if (token.Prev != null &&
          PosToIndentations(token.Prev.pos).Below is var indentation2 and not -1) {
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

  // 'above' is the hypothetical indentation of a comment attached to that token on the line before
  // 'inline' is the hypothetical indentation of this token if it was on its own line
  // 'below' is the hypothetical indentation of a comment after that token, and of the next token if it does not have a set indentation
  public void SetIndentations(IToken token, int above = -1, int inline = -1, int below = -1) {
    if (token is IncludeToken || (token.line == 0 && token.col == 0)) {
      // Just ignore this token.
      return;
    }

    if (above >= 0) {
      PosToIndentations(token.pos).Above = above;
    }

    if (inline >= 0) {
      PosToIndentations(token.pos).Inline = inline;
    }

    if (below >= 0) {
      PosToIndentations(token.pos).Below = below;
    }
  }

  // functions, methods, predicates, iterators, can all be formatted using this method.
  // See FormatterWorksForMethodsInModule in Formatter.cs to see how methods are formatted.
  public void SetMethodLikeIndent(IToken startToken, IEnumerable<IToken> ownedTokens, int indent) {
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
        case "}" when PosToIndentations(token.pos).Inline == -1:
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
              // In the future, we might want to use this to reduce blockiness as well
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

    var indent = GetIndentInlineOrAbove(tokens[0]);
    if (tokens.Count > 1) {
      SetIndentations(tokens[0], below: indent + 2);
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

  // ReSharper disable once UnusedParameter.Local
  void SetAttributeIndentation(Attributes attributes) {
    // If we ever need multiline attributes, here is the place to format them appropriatedly
  }

  public void SetDecreasesExpressionIndentation(Expression expression, int indent) {
    SetExpressionIndentation(expression);
    SetIndentations(expression.EndToken, below: indent);
  }

  public void SetAttributedExpressionIndentation(AttributedExpression attrExpression, int indent) {
    SetAttributeIndentation(attrExpression.Attributes);
    SetExpressionIndentation(attrExpression.E);
    SetIndentations(attrExpression.E.EndToken, below: indent);
  }

  public void SetFrameExpressionIndentation(FrameExpression frameExpression, int indent) {
    SetExpressionIndentation(frameExpression.E);
    SetIndentations(frameExpression.E.EndToken, below: indent);
  }

  public void SetExpressionIndentation(Expression expression) {
    if (expression != null) {
      Visit(expression, GetIndentInlineOrAbove(expression.StartToken));
    }
  }

  public void SetStatementIndentation(Statement statement) {
    Visit(statement, 0);
  }

  public void SetDeclIndentation(TopLevelDecl topLevelDecl, int indent) {
    if (topLevelDecl.tok is IncludeToken) {
      return;
    }

    var indent2 = indent + SpaceTab;
    if (topLevelDecl.StartToken.line > 0) {
      SetDelimiterIndentedRegions(topLevelDecl.BodyStartTok, indent);
      SetOpeningIndentedRegion(topLevelDecl.StartToken, indent);
    }

    if (topLevelDecl is ICanFormat declCanFormat && topLevelDecl is not TopLevelDeclWithMembers) {
      declCanFormat.SetIndent(indent, this);
    } else if (topLevelDecl is TopLevelDeclWithMembers declWithMembers) {
      if (topLevelDecl is ICanFormat canFormat) {
        canFormat.SetIndent(indent, this);
      } else if (declWithMembers is RedirectingTypeDecl redirectingTypeDecl) {
        SetRedirectingTypeDeclDeclIndentation(indent, redirectingTypeDecl);
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
    if (member is ICanFormat canFormat) {
      canFormat.SetIndent(indent, this);
    } else {
      SetMethodLikeIndent(member.StartToken, member.OwnedTokens, indent);
      if (member.BodyStartTok.line > 0) {
        SetDelimiterIndentedRegions(member.BodyStartTok, indent);
      }
    }

    PosToIndentations(member.EndToken.pos).Below = indent;
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
      SetIndentations(subsetTypeDecl.EndToken, below: indent);
    } else if (redirectingTypeDecl is NewtypeDecl newtypeDecl) {
      SetExpressionIndentation(newtypeDecl.Constraint);
      SetExpressionIndentation(newtypeDecl.Witness);
      if (newtypeDecl.Var != null) {
        SetTypeIndentation(newtypeDecl.Var.SyntacticType);
      }

      SetIndentations(newtypeDecl.EndToken, below: indent);
    } else if (redirectingTypeDecl is TypeSynonymDecl typeSynonymDecl) {
      SetIndentations(typeSynonymDecl.EndToken, below: indent);
    }
  }

  public void SetFormalsIndentation(List<Formal> ctorFormals) {
    foreach (var formal in ctorFormals) {
      SetTypeIndentation(formal.SyntacticType);
    }
  }

  // All SetIndent* methods

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
        ? indent
        : indent + SpaceTab;
    var startToken = stmt.StartToken;
    int startAssignmentIndent = inner ? indent + SpaceTab : indent;
    int afterStartIndent = indent + SpaceTab;
    var rightIndent = indent + SpaceTab;
    var commaIndent = indent + SpaceTab;
    SetIndentations(startToken, startAssignmentIndent, startAssignmentIndent, afterStartIndent);

    var rhss = stmt is UpdateStmt updateStmt ? updateStmt.Rhss
      : stmt is AssignOrReturnStmt assignOrReturnStmt ? new List<AssignmentRhs> { assignOrReturnStmt.Rhs }
        .Concat(assignOrReturnStmt.Rhss).ToList()
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
              IsFollowedByNewline(token) ? itemIndent + SpaceTab : itemIndent);

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
              caseIndent = GetIndentInlineOrAbove(token.Prev);
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
        case ",": {
            // For decreases clauses
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
          SetIndentations(token.Prev, below: caseIndent);
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
            isAmpVar ? ampVarIndent : afterSemicolonIndent);
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
        case ",": {
            // For decreases clauses
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

  public bool TryGetIndentAbove(IToken token, out int indent) {
    if (PosToIndentations(token.pos).Above is var aboveIndent and not -1) {
      indent = aboveIndent;
      return true;
    }

    indent = 0;
    return false;
  }

  public bool TryGetIndentInline(IToken token, out int indent) {
    if (PosToIndentations(token.pos).Inline is var inlineIndent and not -1) {
      indent = inlineIndent;
      return true;
    }

    indent = 0;
    return false;
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
  public void SetClosingIndentedRegionAligned(IToken token, int beforeIndent, int indent) {
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
  public void SetClosingIndentedRegionInside(IToken token, int indent) {
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
    SetIndentations(token, below: rightIndent);
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
}