using System;
using System.Collections.Generic;
using System.Linq;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Threading;
using static Microsoft.Dafny.ParseErrors;

namespace Microsoft.Dafny;

public partial class Parser {

  public Parser(DafnyOptions options, Scanner/*!*/ scanner, Errors/*!*/ errors, CancellationToken cancellationToken)
    : this(scanner, errors, cancellationToken)  // the real work
  {
    // initialize readonly fields
    dummyExpr = new LiteralExpr(Token.NoToken);
    dummyRhs = new ExprRhs(dummyExpr);
    dummyFrameExpr = new FrameExpression(dummyExpr.Tok, dummyExpr, null);
    dummyStmt = new ReturnStmt(Token.NoToken, null);
    var dummyBlockStmt = new BlockStmt(Token.NoToken, new List<Statement>());
    dummyIfStmt = new IfStmt(Token.NoToken, false, null, dummyBlockStmt, null);

    theOptions = new DafnyOptions(options);
    theModule = new FileModuleDefinition(scanner.FirstToken);
  }

  public void MergeInto(ref Attributes attrsStack, ref Attributes attrsTarget) {
    Attributes.MergeInto(ref attrsStack, ref attrsTarget);
  }

  public Attributes Consume(ref Attributes attrs) {
    return Attributes.Consume(ref attrs);
  }

  bool IsReveal(IOrigin nextToken) => la.kind == _reveal || (la.kind == _hide && nextToken.kind is _star or _ident);

  bool IsIdentifier(int kind) {
    return kind == _ident || kind == _least || kind == _greatest || kind == _older || kind == _opaque;
  }

  bool IsQuantifierVariableDecl(QuantifiedVar previousVar) {
    // Introducing per-quantified variable ranges creates some ambiguities in the grammar,
    // since before that the range would terminate the quantifed domain. For example, the following statement:
    //
    // print set x | E, y;
    //
    // This would previously parse as two separate arguments to the print statement, but
    // could now also be parsed as a single set comprehension argument with two quantified variables
    // (and an invalid one since it would need an explicit ":: <Term>" section).
    //
    // Even worse:
    //
    // print set x | E, y <- C;
    //
    // This was a valid statement before as well, because "y <- C" would be parsed as the expression
    // "y < (-C)".
    //
    // The /quantifierSyntax option is used to help migrate this otherwise breaking change:
    // * /quantifierSyntax:3 keeps the old behaviour where a "| <Range>" always terminates the list of quantified variables.
    // * /quantifierSyntax:4 instead attempts to parse additional quantified variables.
    if (previousVar.Range != null && theOptions.QuantifierSyntax == QuantifierSyntaxOptions.Version3) {
      return false;
    }

    scanner.ResetPeek();
    IOrigin x = scanner.Peek();
    return la.kind == _comma && IsIdentifier(x.kind);
  }

  // Checks for "<-", which has to be parsed as two separate tokens,
  // but ensures no whitespace between them.
  bool IsFromArrow() {
    scanner.ResetPeek();
    IOrigin x = scanner.Peek();
    return la.kind == _openAngleBracket && x.kind == _minus
      && la.line == x.line && la.col == x.col - 1;
  }

  bool IsLabel(bool allowLabel) {
    if (!allowLabel) {
      return false;
    }
    scanner.ResetPeek();
    IOrigin x = scanner.Peek();
    return (IsIdentifier(la.kind) || la.kind == _digits) && x.kind == _colon;
  }

  bool IsKeywordForFormal() {
    scanner.ResetPeek();
    if (la.kind == _ghost || la.kind == _new || la.kind == _nameonly) {
      return true;
    } else if (la.kind == _older) {
      // "older" is just a contextual keyword, so don't recognize it as a keyword if it must be an identifier
      IOrigin x = scanner.Peek();
      return x.kind != _colon;
    }
    return false;
  }

  bool IsBinding() {
    scanner.ResetPeek();
    IOrigin x = scanner.Peek();
    return (IsIdentifier(la.kind) || la.kind == _digits) && x.kind == _gets;
  }

  bool IsAlternative() {
    IOrigin x = scanner.Peek();
    return (la.kind == _lbrace && x.kind == _case)
        || la.kind == _case;
  }

  bool IsParenIdentsColon() {
    IOrigin x = la;
    if (x.kind != _openparen) {
      return false;
    }
    x = scanner.Peek();
    var oneOrMoreIdentifiers = false;
    while (IsIdentifier(x.kind) || x.kind == _ghost) { /* ghost is illegal here, but checking for it allows better error messages and recovery */
      x = scanner.Peek();
      oneOrMoreIdentifiers = true;
    }
    return oneOrMoreIdentifiers && x.kind == _colon;
  }

  bool IsGets() {
    return la.kind == _gets;
  }

  bool IsPeekVar() {
    scanner.ResetPeek();
    IOrigin x = scanner.Peek();
    return x.kind == _var;
  }

  // an existential guard starts with an identifier and is then followed by
  // * a colon (if the first identifier is given an explicit type),
  // * a comma (if there's a list of bound variables and the first one is not given an explicit type),
  // * a start-attribute (if there's one bound variable and it is not given an explicit type and there are attributes), or
  // * a bored smiley (if there's one bound variable and it is not given an explicit type).
  bool IsBindingGuard() {
    scanner.ResetPeek();
    if (IsIdentifier(la.kind)) {
      Token x = scanner.Peek();
      if (x.kind == _colon || x.kind == _comma || x.kind == _boredSmiley || x.kind == _lbracecolon) {
        return true;
      }
    }
    return false;
  }

  bool IsLoopSpec() {
    return la.kind == _invariant || la.kind == _decreases || la.kind == _modifies;
  }

  bool IsWitness() {
    scanner.ResetPeek();
    if (la.kind == _witness) {
      return true;
    } else if (la.kind == _ghost) {
      Token x = scanner.Peek();
      return x.kind == _witness;
    }
    return false;
  }

  bool IsFunctionDecl() {
    var kind = la.kind;
    return IsFunctionDecl(kind);
  }

  bool IsDecreasesTo() {
    scanner.ResetPeek();
    if (la.kind is _decreases or _nonincreases) {
      Token x = scanner.Peek();
      if (x.kind == _ident && x.val == "to") {
        return true;
      }
    }
    return false;
  }

  private bool IsFunctionDecl(int kind) {
    switch (kind) {
      case _function:
      case _predicate:
      case _copredicate:
        return true;
      case _least:
      case _greatest:
      case _inductive:
        return scanner.Peek().kind != _lemma;
      case _twostate:
        var x = scanner.Peek();
        return x.kind == _function || x.kind == _predicate;
      default:
        return false;
    }
  }

  bool IsParenStar() {
    scanner.ResetPeek();
    Token x = scanner.Peek();
    return la.kind == _openparen && x.kind == _star;
  }

  bool IsEquivOp() => IsEquivOp(la);
  bool IsImpliesOp() => IsImpliesOp(la);
  bool IsExpliesOp() => IsExpliesOp(la);
  bool IsAndOp() => IsAndOp(la);
  bool IsOrOp() => IsOrOp(la);
  bool IsComma() {
    return la.val == ",";
  }
  static bool IsEquivOp(IOrigin la) {
    return la.val == "<==>";
  }
  static bool IsImpliesOp(IOrigin la) {
    return la.val == "==>";
  }
  static bool IsExpliesOp(IOrigin la) {
    return la.val == "<==";
  }
  static bool IsAndOp(IOrigin la) {
    return la.val == "&&";
  }
  static bool IsOrOp(IOrigin la) {
    return la.val == "||";
  }
  bool IsBitwiseAndOp() {
    return la.val == "&";
  }
  bool IsBitwiseOrOp() {
    return la.val == "|";
  }
  bool IsBitwiseXorOp() {
    return la.val == "^";
  }
  bool IsBitwiseOp() {
    return IsBitwiseAndOp() || IsBitwiseOrOp() || IsBitwiseXorOp();
  }
  bool IsAsOrIs() {
    return la.kind == _as || la.kind == _is;
  }
  bool IsRelOp() {
    return la.val == "=="
        || la.val == "<"
        || la.val == ">"
        || la.val == "<="
        || la.val == ">="
        || la.val == "!="
        || la.val == "in"
        || la.kind == _notIn
        || la.val == "!";
  }
  bool IsShiftOp() {
    if (la.kind == _openAngleBracket) {
    } else if (la.kind == _closeAngleBracket) {
    } else {
      return false;
    }
    scanner.ResetPeek();
    var x = scanner.Peek();
    if (x.kind != la.kind) {
      return false;
    }
    return x.pos == la.pos + 1;  // return true only if the tokens are adjacent to each other
  }
  bool IsAddOp() {
    return la.val == "+" || la.val == "-";
  }
  bool IsMulOp() {
    return la.kind == _star || la.val == "/" || la.val == "%";
  }
  bool IsQSep() {
    return la.kind == _doublecolon;
  }

  bool IsNonFinalColon() {
    return la.kind == _colon && scanner.Peek().kind != _rbracket;
  }

  bool ExprIsMapDisplay() {
    scanner.ResetPeek();
    return (la.kind == _map || la.kind == _imap) && scanner.Peek().kind == _lbracket;
  }

  bool ExprIsSetDisplay() {
    scanner.ResetPeek();
    if (la.kind == _lbrace) {
      return true;
    }

    int k = scanner.Peek().kind;
    if (la.kind == _iset && k == _lbrace) {
      return true;
    }

    if (la.kind == _multiset) {
      return true;
    }

    return false;
  }

  bool IsSuffix() {
    return la.kind == _dot || la.kind == _lbracket || la.kind == _openparen;
  }

  string UnwildIdent(IOrigin x, bool allowWildcardId) {
    if (x.val.StartsWith("_")) {
      if (allowWildcardId && x.val.Length == 1) {
        return "_v" + anonymousIds++;
      } else {
        SemErr(ErrorId.p_no_leading_underscore, x, "cannot declare identifier beginning with underscore");
      }
    }
    return x.val;
  }

  bool IsLambda(bool allowLambda) {
    if (!allowLambda) {
      return false;
    }
    scanner.ResetPeek();
    Token x;
    // peek at what might be a signature of a lambda expression
    if (IsIdentifier(la.kind)) {
      // cool, that's the entire candidate signature
    } else if (la.kind != _openparen) {
      return false;  // this is not a lambda expression
    } else {
      int identCount = 0;
      x = scanner.Peek();
      while (x.kind != _closeparen) {
        if (identCount != 0) {
          if (x.kind != _comma) {
            return false;  // not the signature of a lambda
          }
          x = scanner.Peek();
        }
        if (!IsIdentifier(x.kind)) {
          return false;  // not a lambda expression
        }
        identCount++;
        x = scanner.Peek();
        if (x.kind == _colon) {
          // a colon belongs only in a lamdba signature, so this must be a lambda (or something ill-formed)
          return true;
        }
      }
    }
    // What we have seen so far could have been a lambda signature or could have been some
    // other expression (in particular, an identifier, a parenthesized identifier, or a
    // tuple all of whose subexpressions are identifiers).
    // It is a lambda expression if what follows is something that must be a lambda.
    x = scanner.Peek();
    return x.kind == _darrow || x.kind == _reads || x.kind == _requires;
  }

  bool IsIdentParen() {
    scanner.ResetPeek();
    Token x = scanner.Peek();
    return IsIdentifier(la.kind) && x.kind == _openparen;
  }

  /* Used to disambiguate the LHS of a VarDeclStmt. If it looks like the start of a CasePattern,
   * we consider it to be a VarDeclPattern. But if we are looking at a simple identifier, then we
   * consider it to be a VarDeclStmt.
   */
  bool IsPatternDecl() {
    return IsIdentParen() || la.kind == _openparen;
  }

  bool IsIdentColonOrBar() {
    Token x = scanner.Peek();
    return IsIdentifier(la.kind) && (x.kind == _colon || x.kind == _verticalbar);
  }

  bool SemiFollowsCall(bool allowLemma, Expression e) {
    return allowLemma && la.kind == _semicolon && e is ApplySuffix;
  }

  bool IsNotEndOfCase() {
    return la.kind != _EOF && la.kind != _rbrace && la.kind != _case;
  }

  /* The following is the largest lookahead there is. It needs to check if what follows
   * can be nothing but "<" Type { "," Type } ">".
   * If inExpressionContext == true, it also checks the token immediately after
   * the ">" to help disambiguate some cases (see implementation comment).   
   */
  bool IsGenericInstantiation(bool inExpressionContext) {
    scanner.ResetPeek();
    IOrigin pt = la;
    if (!IsTypeList(ref pt)) {
      return false;
    }
    if (!inExpressionContext) {
      return true;
    }
    /* There are ambiguities in the parsing.  For example:
     *     F( a < b , c > (d) )
     * can either be a unary function F whose argument is a function "a" with type arguments "<b,c>" and
     * parameter "d", or can be a binary function F with the two boolean arguments "a < b" and "c > (d)".
     * To make the situation a little better, we (somewhat heuristically) look at the character that
     * follows the ">".  Note that if we, contrary to a user's intentions, pick "a<b,c>" out as a function
     * with a type instantiation, the user can disambiguate it by making sure the ">" sits inside some
     * parentheses, like:
     *     F( a < b , (c > (d)) )
     */
    // In the following cases, we're sure we must have read a type instantiation that just ended an expression
    if (IsEquivOp(pt) || IsImpliesOp(pt) || IsExpliesOp(pt) || IsAndOp(pt) || IsOrOp(pt)) {
      return true;
    }
    switch (pt.kind) {
      case _dot:  // here, we're sure it must have been a type instantiation we saw, because an expression cannot begin with dot
      case _openparen:  // it was probably a type instantiation of a function/method
      case _lbracket:  // it is possible that it was a type instantiation
      case _lbrace:  // it was probably a type instantiation of a function/method
      case _at:
      // In the following cases, we're sure we must have read a type instantiation that just ended an expression
      case _closeparen:
      case _rbracket:
      case _rbrace:
      case _comma:
      case _semicolon:
      case _then:
      case _else:
      case _case:
      case _eq:
      case _neq:
      case _as:
      case _is:
      case _darrow:
      case _by:
      case _in:
      case _openAngleBracket:
      case _closeAngleBracket:
      case _EOF:
      // (specification clauses that can follow an expression)
      case _decreases:
      case _modifies:
      case _reads:
      case _requires:
      case _ensures:
      case _invariant:
      case _witness:
      // (top-level declarations that can follow an expression)
      case _function:
      case _predicate:
      case _least:
      case _greatest:
      case _inductive:
      case _twostate:
      case _lemma:
      case _copredicate:
      case _ghost:
      case _static:
      case _import:
      case _export:
      case _class:
      case _trait:
      case _datatype:
      case _codatatype:
      case _var:
      case _const:
      case _newtype:
      case _type:
      case _iterator:
      case _method:
      case _colemma:
      case _constructor:
        return true;
      default:
        return false;
    }
  }

  // Returns true if the parser can parse an heap-referencing @-call
  // The reason to do this is that expressions can be prefixed by @-Attributes,
  // so the rule to distinguish them is that an @-call of the form name@label(args),
  // the @ must be next to the name. Otherwise an attribute is parsed.
  // Indeed 'name' could be the last expression of an ensures clause, and the attribute
  // could belong to the next method declaration otherwise.
  bool IsAtCall() {
    IOrigin pt = la;
    if (pt.val != "@") {
      return false;
    }
    // If it's the beginning of the file, or the previous token is on a different line or separated by a space, it's not an At-call. Must be an attribute
    var isFirstToken = pt.Prev == null;
    var spaceExistsSincePreviousToken =
      !isFirstToken &&
      (pt.Prev.line != pt.line || pt.Prev.col + pt.Prev.val.Length + pt.TrailingTrivia.Trim().Length < pt.col - pt.LeadingTrivia.Trim().Length);
    if (isFirstToken || spaceExistsSincePreviousToken) {
      return false;
    }

    return true;
  }

  /* Returns true if the next thing is of the form:
   *     "<" Type { "," Type } ">"
   */
  bool IsTypeList(ref IOrigin pt) {
    if (pt.kind != _openAngleBracket) {
      return false;
    }
    pt = scanner.Peek();
    return IsTypeSequence(ref pt, _closeAngleBracket);
  }
  /* Returns true if the next thing is of the form:
   *     [ "ghost" ] Type { "," [ "ghost" ] Type }
   * followed by an endBracketKind.
   */
  bool IsTypeSequence(ref IOrigin pt, int endBracketKind) {
    while (true) {
      if (pt.kind == _ghost) {
        pt = scanner.Peek();
      }
      if (!IsType(ref pt)) {
        return false;
      }
      if (pt.kind == endBracketKind) {
        // end of type list
        pt = scanner.Peek();
        return true;
      } else if (pt.kind == _comma) {
        // type list continues
        pt = scanner.Peek();
      } else {
        // not a type list
        return false;
      }
    }
  }

  bool IsType(ref IOrigin pt) {
    if (!IsNonArrowType(ref pt)) {
      return false;
    }

    while (pt.kind == _sarrow || pt.kind == _qarrow || pt.kind == _larrow) {
      pt = scanner.Peek();
      if (!IsNonArrowType(ref pt)) {
        return false;
      }
    }
    return true;
  }

  bool IsNonArrowType(ref IOrigin pt) {
    switch (pt.kind) {
      case _bool:
      case _char:
      case _nat:
      case _int:
      case _real:
      case _ORDINAL:
      case _string:
      case _object_q:
      case _object:
        pt = scanner.Peek();
        return true;
      case _arrayToken:
      case _bvToken:
      case _set:
      case _iset:
      case _multiset:
      case _seq:
      case _map:
      case _imap:
        pt = scanner.Peek();
        return pt.kind != _openAngleBracket || IsTypeList(ref pt);
      case _ident:
      case _least:
      case _greatest:
        while (true) {
          // invariant: next token is an identifier (_ident, _least, or _greatest)
          pt = scanner.Peek();
          if (pt.kind == _openAngleBracket && !IsTypeList(ref pt)) {
            return false;
          }
          if (pt.kind != _dot) {
            // end of the type
            return true;
          }
          pt = scanner.Peek();  // get the _dot
          if (!IsIdentifier(pt.kind)) {
            return false;
          }
        }
      case _openparen:
        pt = scanner.Peek();
        if (pt.kind == _closeparen) {
          // end of type list
          pt = scanner.Peek();
          return true;
        }
        return IsTypeSequence(ref pt, _closeparen);
      default:
        return false;
    }
  }


  void ConvertKeywordTokenToIdent() {
    var oldKind = la.kind;
    la.kind = _ident;

    // call CheckLiteral with la
    var origT = t;
    t = la;
    scanner.CheckLiteral();
    t = origT;

    if (la.kind != _ident) {
      // it has been changed by CheckLiteral, which means it was a keyword
      la.kind = _ident;  // convert it to an ident
    } else {
      // la was something other than a keyword
      la.kind = oldKind;
    }
  }

  int StringToInt(string s, int defaultValue, string errString, IOrigin tok) {
    Contract.Requires(s != null);
    Contract.Requires(errString != null);
    try {
      if (s != "") {
        defaultValue = int.Parse(s);
      }
    } catch (System.OverflowException) {
      SemErr(errString.Contains("array") ? ErrorId.p_array_dimension_too_large
                                         : ErrorId.p_bitvector_too_large,
        tok, string.Format("sorry, {0} ({1}) are not supported", errString, s));
    }
    return defaultValue;
  }

  readonly Expression/*!*/ dummyExpr;
  readonly AssignmentRhs/*!*/ dummyRhs;
  readonly FrameExpression/*!*/ dummyFrameExpr;
  readonly Statement/*!*/ dummyStmt;
  readonly Statement/*!*/ dummyIfStmt;
  public readonly FileModuleDefinition theModule;
  public readonly List<Action<SystemModuleManager>> SystemModuleModifiers = new();
  DafnyOptions theOptions;
  int anonymousIds = 0;

  /// <summary>
  /// Holds the modifiers and attributes given for a declaration
  ///
  /// Not all modifiers are applicable to all kinds of declarations.
  /// Errors are given when a modify does not apply.
  /// We also record the tokens for the specified modifiers so that
  /// they can be used in error messages.
  /// </summary>
  class DeclModifierData {
    public bool IsReplaceable;
    public IOrigin ReplaceableToken;
    public bool IsAbstract;
    public IOrigin AbstractToken;
    public bool IsGhost;
    public IOrigin GhostToken;
    public bool IsStatic;
    public IOrigin StaticToken;
    public bool IsOpaque;
    public IOrigin OpaqueToken;
    public Token FirstTokenExceptAttributes;
    public Attributes Attributes = null;

    public Token FirstToken {
      get {
        Token result = FirstTokenExceptAttributes;
        foreach (var attr in Attributes.AsEnumerable()) {
          if (result == null || result.pos > attr.Tok.pos) {
            result = attr.StartToken;
          }
        }

        return result;
      }
    }
  }

  private ModuleKindEnum GetModuleKind(DeclModifierData mods) {
    if (mods.IsReplaceable && mods.IsAbstract) {
      SemErr(null, mods.ReplaceableToken, "Can't be both replaceable and abstract");
    }

    if (mods.IsReplaceable) {
      return ModuleKindEnum.Replaceable;
    }
    if (mods.IsAbstract) {
      return ModuleKindEnum.Abstract;
    }

    return ModuleKindEnum.Concrete;
  }

  /// <summary>
  /// Before literals that end a block, we usually add CheckNoAttributes to avoid any non-attached or dangling attributes
  /// </summary>
  public void CheckNoAttributes(ref Attributes attrs) {
    if (attrs != null) {
      SemErr(ErrorId.p_extra_attributes, attrs.Origin, "Attribute not expected here");
      attrs = null;
    }
  }

  // Check that token has not been set, then set it.
  public void CheckAndSetToken(ref IOrigin token) {
    if (token != null) {
      SemErr(ErrorId.p_duplicate_modifier, t, "Duplicate declaration modifier: " + t.val);
    }
    token = t;
  }

  // Check that token has not been set, then set it, but just ignores if it was set already
  public void CheckAndSetTokenOnce(ref Token token) {
    if (token == null) {
      token = t;
    }
  }

  /// <summary>
  // A flags type used to tell what declaration modifiers are allowed for a declaration.
  /// </summary>
  [Flags]
  enum AllowedDeclModifiers {
    None = 0,
    Abstract = 1,
    Ghost = 2,

    // Means ghost not allowed because already implicitly ghost.
    AlreadyGhost = 4,
    Static = 8,
    Opaque = 16,
    Replaceable = 32
  };

  bool CheckAttribute(Errors errors, IOrigin attr, SourceOrigin range) {
    // attr is the identifier of the Attribute
    // range is from opening brace to closing brace
    if (attr.val == "ignore") {
      errors.Warning(ErrorId.p_deprecated_attribute,
        range,
        $"attribute :{attr.val} is deprecated");
      return false;
    }
    return true;
  }

  bool IsAssumeTypeKeyword(IOrigin la) {
    return la.kind == _assume || la.kind == _assert || la.kind == _expect;
  }

  Expression ProcessTupleArgs(List<ActualBinding> args, IOrigin lp) {
    if (args.Count == 1 && !args[0].IsGhost) {
      if (args[0].FormalParameterName != null) {
        SemErr(ErrorId.p_no_parenthesized_binding, lp, "binding not allowed in parenthesized expression");
      }
      return args[0].Actual;
    } else {
      // Compute the actual position of ghost arguments
      var ghostness = new bool[args.Count];
      for (var i = 0; i < args.Count; i++) {
        ghostness[i] = false;
      }
      for (var i = 0; i < args.Count; i++) {
        var arg = args[i];
        if (arg.IsGhost) {
          if (arg.FormalParameterName == null) {
            ghostness[i] = true;
          } else {
            var success = int.TryParse(arg.FormalParameterName.val, out var index);
            if (success && 0 <= index && index < args.Count) {
              ghostness[index] = true;
            }
          }
        }
      }
      var argumentGhostness = ghostness.ToList();
      // make sure the corresponding tuple type exists
      SystemModuleModifiers.Add(b => b.TupleType(lp, args.Count, true, argumentGhostness));
      return new DatatypeValue(lp, SystemModuleManager.TupleTypeName(argumentGhostness), SystemModuleManager.TupleTypeCtorName(args.Count), args);
    }
  }


  public void ApplyOptionsFromAttributes(Attributes attrs) {
    var overrides = attrs.AsEnumerable().Where(a => a.Name == "options" || a is UserSuppliedAtAttribute { UserSuppliedName: "Options" })
      .Reverse().Select(a =>
        (token: a.Tok,
         options: UserSuppliedAtAttribute.GetUserSuppliedArguments(a).Select(arg => {
           if (arg is not LiteralExpr { Value: string optStr }) {
             SemErr(ErrorId.p_literal_string_required, arg.Tok, "argument to :options attribute must be a literal string");
             return null;
           }
           return optStr;
         }).Where(opt => opt != null).ToArray()))
      .Where(opts => opts.options.Any());

    if (overrides.Any()) {
      var options = new DafnyAttributeOptions(theOptions, errors);
      foreach (var (token, opts) in overrides) {

        var newOptionsCommand = new RootCommand();
        newOptionsCommand.AddOption(CommonOptionBag.QuantifierSyntax);
        newOptionsCommand.AddOption(Function.FunctionSyntaxOption);
        var result = newOptionsCommand.Parse(string.Join(' ', opts));

        if (!result.Errors.Any()) {
          foreach (var option in newOptionsCommand.Options) {
            var value = result.GetValueForOption(option);
            options.Options.OptionArguments[option] = value;
            options.ApplyBinding(option);
          }
          continue;
        }

        options.Token = token;
        options.Parse(opts);
      }
      theOptions = options;
    }
  }

  /// <summary>
  /// Check the declaration modifiers against those that are allowed.
  ///
  /// The 'allowed' parameter specifies which declaration modifiers are allowed.
  /// The 'declCaption' parameter should be a string describing the kind of declaration.
  /// It is used in error messages.
  /// Any declaration modifiers that are present but not allowed are cleared.
  ///</summary>
  void CheckDeclModifiers(ref DeclModifierData dmod, string declCaption, AllowedDeclModifiers allowed) {
    declCaption = (declCaption.StartsWith("i") || declCaption.StartsWith("o") ? "an " : "a ") + declCaption;
    if (dmod.IsAbstract && ((allowed & AllowedDeclModifiers.Abstract) == 0)) {
      SemErr(ErrorId.p_abstract_not_allowed, dmod.AbstractToken, $"{declCaption} cannot be declared 'abstract'");
      dmod.IsAbstract = false;
    }
    if (dmod.IsReplaceable && ((allowed & AllowedDeclModifiers.Replaceable) == 0)) {
      SemErr(ErrorId.p_abstract_not_allowed, dmod.ReplaceableToken, $"{declCaption} cannot be declared 'replaceable'");
      dmod.IsReplaceable = false;
    }
    if (dmod.IsGhost) {
      if ((allowed & AllowedDeclModifiers.AlreadyGhost) != 0) {
        if (declCaption.Contains("-by-method")) {
          SemErr(ErrorId.p_no_ghost_for_by_method, dmod.GhostToken,
            $"{declCaption} has a ghost function body and a non-ghost method body; {declCaption} declaration does not use the 'ghost' keyword.");
        } else if (declCaption == "a function" || declCaption == "a predicate") {
          SemErr(ErrorId.p_ghost_forbidden_default_3, dmod.GhostToken, $"{declCaption} cannot be declared 'ghost' (it is 'ghost' by default when using --function-syntax:3)");
        } else {
          SemErr(ErrorId.p_ghost_forbidden_default, dmod.GhostToken, $"{declCaption} cannot be declared 'ghost' (it is 'ghost' by default)");
        }
        dmod.IsGhost = false;
      } else if ((allowed & AllowedDeclModifiers.Ghost) == 0) {
        SemErr(ErrorId.p_ghost_forbidden, dmod.GhostToken, $"{declCaption} cannot be declared 'ghost'");
        dmod.IsGhost = false;
      }
    }
    if (dmod.IsStatic && ((allowed & AllowedDeclModifiers.Static) == 0)) {
      SemErr(ErrorId.p_no_static, dmod.StaticToken, $"{declCaption} cannot be declared 'static'");
      dmod.IsStatic = false;
    }
    if (dmod.IsOpaque && ((allowed & AllowedDeclModifiers.Opaque) == 0)) {
      SemErr(ErrorId.p_no_opaque, dmod.OpaqueToken, $"{declCaption} cannot be declared 'opaque'");
      dmod.IsOpaque = false;
    }
  }

}
