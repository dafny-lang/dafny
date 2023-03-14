using System;
using System.Collections.Generic;
using System.Configuration;
using System.Diagnostics.Contracts;
using System.Linq;
using static Microsoft.Dafny.ErrorRegistry;

namespace Microsoft.Dafny; 

/// <summary>
/// Removes nesting from matching patterns, such as case Cons(head1, Cons(head2, tail))
///
/// match xs {
///   case Cons(y, Cons(z, zs)) =>
///   return z;
///   case Cons(y, Nil()) =>
///   return y;
///   case Nil() =>
///   return 0;
/// }
///
/// Is translated to
/// 
/// match xs {
///   case Nil =>
///     return 0;
///   case Cons(_mcc#0: int, _mcc#1: List<int>) =>
///     match _mcc#1 {
///       case Nil =>
///         var y: int := _mcc#0;
///         return y;
///       case Cons(_mcc#2: int, _mcc#3: List<int>) =>
///         var zs: List<int> := _mcc#3;
///         var z: int := _mcc#2;
///         var y: int := _mcc#0;
///         return z;
///   }
/// }
///
/// 
/// </summary>
public class MatchFlattener : IRewriter {
  private const string NoCasesMessage = "match has no cases and this is only allowed when the verifier can prove the match is unreachable";
  private readonly FreshIdGenerator idGenerator;
  private ResolutionContext resolutionContext;

  public MatchFlattener(ErrorReporter reporter, FreshIdGenerator idGenerator)
    : base(reporter) {
    this.idGenerator = idGenerator;
  }

  internal override void PostResolve(Program program) {
    foreach (var compileModule in program.RawModules()) {
      FlattenNode(compileModule);
    }
    foreach (var compileModule in program.CompileModules) {
      var reporter = Reporter;
      Reporter = new ErrorReporterSink(program.Options);
      FlattenNode(compileModule);
      Reporter = reporter;
    }
  }

  private void FlattenNode(Node root) {
    root.Visit(node => {
      if (node != root && node is ModuleDefinition) {
        // The resolver clones module definitions for compilation, but also the top level module which also contains the uncloned definitions,
        // so this is to prevent recursion into the uncloned definitions. 
        return false;
      }

      if (node is ICallable callable) {
        resolutionContext = new ResolutionContext(callable, false);
      }

      if (node is NestedMatchStmt nestedMatchStmt) {
        nestedMatchStmt.Flattened = CompileNestedMatchStmt(nestedMatchStmt);
        FlattenNode(nestedMatchStmt.Flattened);
        return false;
      }

      if (node is NestedMatchExpr nestedMatchExpr) {
        nestedMatchExpr.Flattened = CompileNestedMatchExpr(nestedMatchExpr);
        FlattenNode(nestedMatchExpr.Flattened);
        return false;
      }

      return true;
    });
  }


  private Expression CompileNestedMatchExpr(NestedMatchExpr nestedMatchExpr) {
    var cases = nestedMatchExpr.Cases.SelectMany(FlattenNestedMatchCaseExpr).ToList();
    var state = new MatchCompilationState(nestedMatchExpr, cases, resolutionContext);

    var paths = cases.Select((@case, index) => (PatternPath)new ExprPatternPath(index, @case, @case.Attributes)).ToList();

    CaseBody compiledMatch = CompilePatternPaths(state, new HoleCtx(), LinkedLists.Create(nestedMatchExpr.Source), paths);
    if (compiledMatch is null) {
      if (nestedMatchExpr.Source.Type.AsDatatype == null) {
        var havoc = LetExpr.Havoc(nestedMatchExpr.tok, nestedMatchExpr.Type);
        return new StmtExpr(nestedMatchExpr.tok, AssertStmt.CreateErrorAssert(nestedMatchExpr, NoCasesMessage), havoc) {
          Type = nestedMatchExpr.Type
        };
      }

      return new MatchExpr(nestedMatchExpr.tok, nestedMatchExpr.Source, new List<MatchCaseExpr>(),
        nestedMatchExpr.UsesOptionalBraces) {
        Type = nestedMatchExpr.Type
      };
    }

    if (compiledMatch.Node is Expression expression) {
      for (int id = 0; id < state.CaseCopyCount.Length; id++) {
        if (state.CaseCopyCount[id] <= 0) {
          Reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, state.CaseTok[id], "this branch is redundant");
        }
      }
      return expression;
    }
    Contract.Assert(false); throw new cce.UnreachableException(); // Returned container should be a CExpr
  }

  private Statement CompileNestedMatchStmt(NestedMatchStmt nestedMatchStmt) {
    var cases = nestedMatchStmt.Cases.SelectMany(FlattenNestedMatchCaseStmt).ToList();
    var state = new MatchCompilationState(nestedMatchStmt, cases, resolutionContext.WithGhost(nestedMatchStmt.IsGhost), nestedMatchStmt.Attributes);

    var paths = cases.Select((@case, index) => (PatternPath)new StmtPatternPath(index, @case, @case.Attributes)).ToList();

    var compiledMatch = CompilePatternPaths(state, new HoleCtx(), LinkedLists.Create(nestedMatchStmt.Source), paths);
    if (compiledMatch is null) {
      // Happens only if the nested match has no cases
      if (nestedMatchStmt.Source.Type.AsDatatype == null) {
        return AssertStmt.CreateErrorAssert(nestedMatchStmt, NoCasesMessage);
      }

      return new MatchStmt(nestedMatchStmt.RangeToken, nestedMatchStmt.Source, new List<MatchCaseStmt>(), nestedMatchStmt.UsesOptionalBraces, nestedMatchStmt.Attributes);
    }

    if (compiledMatch.Node is Statement statement) {
      var result = statement;
      result.Attributes = (new ClonerKeepParensExpressions()).CloneAttributes(nestedMatchStmt.Attributes);
      for (int id = 0; id < state.CaseCopyCount.Length; id++) {
        if (state.CaseCopyCount[id] <= 0) {
          Reporter.Warning(MessageSource.Resolver, ErrorRegistry.NoneId, state.CaseTok[id], "this branch is redundant");
        }
      }

      new GhostInterestVisitor(resolutionContext.WithGhost(nestedMatchStmt.IsGhost).CodeContext, null, Reporter, false).
        Visit(result, nestedMatchStmt.IsGhost, null);
      return result;
    }
    Contract.Assert(false); throw new cce.UnreachableException(); // Returned container should be a StmtContainer
  }

  private IEnumerable<NestedMatchCaseStmt> FlattenNestedMatchCaseStmt(NestedMatchCaseStmt c) {
    foreach (var pat in FlattenDisjunctivePatterns(c.Pat)) {
      yield return new NestedMatchCaseStmt(c.Tok, pat,
        c.Body,
        c.Attributes);
    }
  }

  private ExtendedPattern RemoveIllegalSubpatterns(ExtendedPattern pat, bool inDisjunctivePattern) {
    switch (pat) {
      case LitPattern:
        return pat;
      case IdPattern p:
        if (inDisjunctivePattern && p.ResolvedLit == null && p.Arguments == null && !p.IsWildcardPattern) {
          return new IdPattern(p.Tok, FreshTempVarName("_", null), null, p.IsGhost);
        }
        var args = p.Arguments?.ConvertAll(a => RemoveIllegalSubpatterns(a, inDisjunctivePattern));
        return new IdPattern(p.Tok, p.Id, p.Type, args, p.IsGhost) { ResolvedLit = p.ResolvedLit, BoundVar = p.BoundVar };
      case DisjunctivePattern p:
        return new IdPattern(p.Tok, FreshTempVarName("_", null), null, p.IsGhost);
      default:
        Contract.Assert(false);
        return null;
    }
  }

  string FreshTempVarName(string prefix, ICodeContext context) {
    var gen = context is Declaration decl ? decl.IdGenerator : idGenerator;
    var freshTempVarName = gen.FreshId(prefix);
    return freshTempVarName;
  }

  private IEnumerable<ExtendedPattern> FlattenDisjunctivePatterns(ExtendedPattern pat) {
    // TODO: Once we rewrite the pattern-matching compiler, we'll handle disjunctive patterns in it, too.
    // For now, we handle top-level disjunctive patterns by duplicating the corresponding cases here, and disjunctive
    // sub-patterns are unsupported.
    return pat is DisjunctivePattern p
      ? p.Alternatives.Select(a => RemoveIllegalSubpatterns(a, inDisjunctivePattern: true))
      : Enumerable.Repeat(RemoveIllegalSubpatterns(pat, inDisjunctivePattern: false), 1);
  }

  private IEnumerable<NestedMatchCaseExpr> FlattenNestedMatchCaseExpr(NestedMatchCaseExpr c) {
    foreach (var pat in FlattenDisjunctivePatterns(c.Pat)) {
      yield return new NestedMatchCaseExpr(c.Tok, pat, c.Body, c.Attributes);
    }
  }

  /// <summary>
  /// Create a decision tree with flattened MatchStmt (or MatchExpr) with disjoint cases and if-constructs
  /// Start with a list of n matchees and list of m paths, each with n patterns and a body
  /// 1 - if m = 0, then no original path exists for the current case, return null
  /// 2 - if n = 0, return the body of the first path
  /// 3** - if the head-matchee is a base type, but some patterns are constants, create if-else construct for one level and recur
  /// 3 - if some of the head-patterns are constructors (including tuples), create one level of matching at the type of the head-matchee,
  ///     recur for each constructor of that datatype
  /// 4 - Otherwise, all head-patterns are variables, let-bind the head-matchee as the head-pattern in each of the bodypatterns,
  ///     continue processing the matchees
  /// </summary>
  private CaseBody CompilePatternPaths(MatchCompilationState state, MatchingContext context, SinglyLinkedList<Expression> matchees, List<PatternPath> paths) {

    // For each path, number of matchees (n) is the number of patterns held by the path
    if (!paths.TrueForAll(x => matchees.Count() == x.Patterns.Count)) {
      Reporter.Error(MessageSource.Resolver, state.Tok, "Match is malformed, make sure constructors are fully applied");
    }

    if (paths.Count == 0) {
      // ==[1]== If no path, then match is not syntactically exhaustive -- return null
      // (Semantics) exhaustiveness is checked by the verifier, so no need for a warning here
      // Reporter.Warning(MessageSource.Resolver, mti.Tok, "non-exhaustive case-statement");
      return null;
    }

    if (matchees is Cons<Expression> consMatchees) {
      return CompilePatternPathsForMatchee(state, context, paths, consMatchees);
    }

    // ==[2]== No more matchees to process, return the first path and decrement the count of dropped paths
    for (int i = 1; i < paths.Count; i++) {
      state.UpdateCaseCopyCount(paths[i].CaseId, -1);
    }

    return PackBody(state.CaseTok[paths.First().CaseId], paths.First());
  }

  private CaseBody CompilePatternPathsForMatchee(MatchCompilationState state, MatchingContext context,
    List<PatternPath> paths, Cons<Expression> consMatchees) {
    // Otherwise, start handling the first matchee
    Expression currMatchee = consMatchees.Head;

    // Get the datatype of the matchee
    var currMatcheeType = currMatchee.Type.NormalizeExpand();

    var dtd = currMatcheeType.AsDatatype;

    // Get all constructors of type matchee
    var subst = new Dictionary<TypeParameter, Type>();
    Dictionary<string, DatatypeCtor> ctors;
    if (dtd == null) {
      ctors = null;
    } else {
      ctors = dtd.Ctors.ToDictionary(c => c.Name, c => c);
      Contract.Assert(ctors != null); // dtd should have been inserted into datatypeCtors during a previous resolution stage
      subst = TypeParameter.SubstitutionMap(dtd.TypeArgs,
        currMatcheeType.TypeArgs); // Build the type-parameter substitution map for this use of the datatype
    }

    // Get the head of each patterns
    var patternHeads = paths.ConvertAll(GetPatternHead);

    if (ctors != null && patternHeads.Exists(x =>
          x is IdPattern { Arguments: { } } pattern && ctors.ContainsKey(pattern.Id))) {
      // ==[3]== If dtd is a datatype and at least one of the pattern heads is a constructor, create a match on currMatchee
      return CompileHeadsContainingConstructor(state, context, consMatchees, subst, ctors, paths);
    } else if (dtd == null && patternHeads.Exists(x => (x is LitPattern || x is IdPattern { ResolvedLit: { } }))) {
      // ==[3**]== If dtd is a base type and at least one of the pattern is a constant, create an If-then-else construct on the constant

      return CompileHeadsContainingLiteralPattern(state, context, consMatchees, paths);
    } else {
      // ==[4]==  all head patterns are bound variables:

      var tailPaths = paths.Select(path => {
        var (head, tail) = SplitPath(path);
        if (!(head is IdPattern)) {
          Contract.Assert(false);
          throw new cce.UnreachableException(); // in Variable case with a constant pattern
        }

        var currPattern = (IdPattern)head;

        if (currPattern.Arguments != null) {
          if (dtd == null) {
            Contract.Assert(false);
            throw new cce.UnreachableException(); // non-nullary constructors of a non-datatype;
          } else {
            Reporter.Error(MessageSource.Resolver, currPattern.Tok,
              "Type mismatch: expected constructor of type {0}.  Got {1}.", dtd.Name, currPattern.Id);
          }
        }

        // Optimization: Don't let-bind if name is a wildcard, either in source or generated
        return LetBindNonWildCard(currPattern, currMatchee, tail);
      }).ToList();

      return CompilePatternPaths(state, context.AbstractHole(), consMatchees.Tail, tailPaths);
    }
  }

  /*
   * Implementation of case 3 (some of the head patterns are constructors) of pattern-match compilation
   * Current matchee is a datatype (with type parameter substitution in subst) with constructors in ctors
   * PairPB contains, for each paths, its head pattern and the rest of the path.
   */
  private CaseBody CompileHeadsContainingConstructor(MatchCompilationState mti, MatchingContext context, Cons<Expression> matchees,
    Dictionary<TypeParameter, Type> subst, Dictionary<string, DatatypeCtor> constructorByName,
    List<PatternPath> paths) {

    var headMatchee = matchees.Head;
    var remainingMatchees = matchees.Tail;
    var newMatchCases = new List<MatchCase>();
    // Update mti -> each path generates up to |ctors| copies of itself
    foreach (var path in paths) {
      mti.UpdateCaseCopyCount(path.CaseId, constructorByName.Count - 1);
    }

    var ctorToFromBoundVar = new HashSet<string>();

    foreach (var ctor in constructorByName.Values) {

      var constructorPaths = new List<PatternPath>();

      // create a bound variable for each formal to use in the MatchCase for this constructor
      // using the currMatchee.tok to get a location closer to the error if something goes wrong
      var freshPatBV = ctor.Formals.ConvertAll(
        x => CreateBoundVariable(headMatchee.tok, x.Type.Subst(subst), mti.CodeContext.CodeContext));

      // rhs to bind to head-patterns that are bound variables
      var rhsExpr = headMatchee;
      var ctorCounter = 0;

      // -- filter paths for each constructor
      foreach (var path in paths) {
        var (head, tail) = SplitPath(path);
        if (head is IdPattern idPattern) {
          if (ctor.Name.Equals(idPattern.Id) && idPattern.Arguments != null) {
            // ==[3.1]== If pattern is same constructor, push the arguments as patterns and add that path to new match
            // After making sure the constructor is applied to the right number of arguments

            if (!(idPattern.Arguments.Count.Equals(ctor.Formals.Count))) {
              Reporter.Error(MessageSource.Resolver, mti.CaseTok[tail.CaseId], "constructor {0} of arity {1} is applied to {2} argument(s)", ctor.Name, ctor.Formals.Count, idPattern.Arguments.Count);
            }
            for (int j = 0; j < idPattern.Arguments.Count; j++) {
              // mark patterns standing in for ghost field
              idPattern.Arguments[j].IsGhost = idPattern.Arguments[j].IsGhost || ctor.Formals[j].IsGhost;
            }
            tail.Patterns.InsertRange(0, idPattern.Arguments);
            constructorPaths.Add(tail);
            ctorCounter++;
          } else if (constructorByName.ContainsKey(idPattern.Id) && idPattern.Arguments != null) {
            // ==[3.2]== If the pattern is a different constructor, drop the path
            mti.UpdateCaseCopyCount(tail.CaseId, -1);
          } else if (idPattern.ResolvedLit != null) {
            // TODO
          } else {
            // ==[3.3]== If the pattern is a bound variable, create new bound variables for each of the arguments of the constructor, and let-binds the matchee as original bound variable
            // n.b. this may duplicate the matchee

            // make sure this potential bound var is not applied to anything, in which case it is likely a mispelled constructor
            if (idPattern.Arguments != null && idPattern.Arguments.Count != 0) {
              Reporter.Error(MessageSource.Resolver, mti.CaseTok[tail.CaseId], "bound variable {0} applied to {1} argument(s).", idPattern.Id, idPattern.Arguments.Count);
            }

            var freshArgs = ctor.Formals.ConvertAll(x =>
              CreateFreshBindingPattern(idPattern.Tok, x.Type.Subst(subst), mti.CodeContext.CodeContext, x.IsGhost));

            tail.Patterns.InsertRange(0, freshArgs);
            var newPath = LetBindNonWildCard(idPattern, rhsExpr, tail);
            constructorPaths.Add(newPath);
            ctorToFromBoundVar.Add(ctor.Name);
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      }
      // Add variables corresponding to the arguments of the current constructor (ctor) to the matchees
      var freshMatchees = freshPatBV.ConvertAll(x => new IdentifierExpr(x.tok, x));
      // Update the current context
      var newContext = context.FillHole(new IdCtx(ctor));
      var body = CompilePatternPaths(mti, newContext, LinkedLists.Concat(freshMatchees, remainingMatchees), constructorPaths);
      if (body is null) {
        // If no path matches this constructor, drop the case
        continue;
      }

      // Otherwise, add the case the new match created at [3]
      var tok = body.Tok ?? new AutoGeneratedToken(headMatchee.tok);
      var fromBoundVar = ctorToFromBoundVar.Contains(ctor.Name);
      var newMatchCase = CreateMatchCase(tok, ctor, freshPatBV, body, fromBoundVar);
      newMatchCases.Add(newMatchCase);
    }

    // Generate and pack the right kind of Match
    if (mti.Match is NestedMatchStmt nestedMatchStmt) {
      var newMatchCaseStmts = newMatchCases.Select(x => (MatchCaseStmt)x).ToList();
      foreach (var c in newMatchCaseStmts) {
        if (Attributes.Contains(c.Attributes, "split")) {
          continue;
        }

        var args = new List<Expression>();
        var literalExpr = new LiteralExpr(mti.Tok, false);
        literalExpr.Type = Type.Bool;
        args.Add(literalExpr);
        c.Attributes = new Attributes("split", args, c.Attributes);
      }
      var newMatchStmt = new MatchStmt(nestedMatchStmt.RangeToken, headMatchee, newMatchCaseStmts, true, mti.Attributes, context);
      newMatchStmt.IsGhost |= mti.CodeContext.IsGhost;
      return new CaseBody(null, newMatchStmt);
    }

    var newMatchExpr = new MatchExpr(mti.Tok, headMatchee, newMatchCases.ConvertAll(x => (MatchCaseExpr)x), true, context);
    newMatchExpr.Type = ((NestedMatchExpr)mti.Match).Type;
    return new CaseBody(null, newMatchExpr);
  }

  private MatchCase CreateMatchCase(IToken tok, DatatypeCtor ctor, List<BoundVar> freshPatBV, CaseBody bodyContainer, bool fromBoundVar) {
    MatchCase newMatchCase;
    var cloner = new Cloner(true);
    if (bodyContainer.Node is Statement statement) {
      var body = UnboxStmt(statement).Select(cloner.CloneStmt).ToList();
      newMatchCase = new MatchCaseStmt(tok.ToRange(), ctor, fromBoundVar, freshPatBV, body, bodyContainer.Attributes);
    } else {
      var body = (Expression)(bodyContainer.Node);
      var attrs = bodyContainer.Attributes;
      newMatchCase = new MatchCaseExpr(tok, ctor, fromBoundVar, freshPatBV, cloner.CloneExpr(body), attrs);
    }
    newMatchCase.Ctor = ctor;
    return newMatchCase;
  }

  private BoundVar CreateBoundVariable(IToken tok, Type type, ICodeContext codeContext) {
    var name = FreshTempVarName("_mcc#", codeContext);
    return new BoundVar(new AutoGeneratedToken(tok), name, type);
  }

  private IdPattern CreateFreshBindingPattern(IToken tok, Type type, ICodeContext codeContext, bool isGhost = false) {
    var name = FreshTempVarName("_mcc#", codeContext);
    return new IdPattern(new AutoGeneratedToken(tok), name, type, null, isGhost);
  }

  /*
   * Implementation of case 3** (some of the head patterns are constants) of pattern-match compilation
   */
  private CaseBody CompileHeadsContainingLiteralPattern(MatchCompilationState mti, MatchingContext context, Cons<Expression> matchees, List<PatternPath> paths) {
    // Decrease the count for each path (increases back for each occurence later on)
    foreach (var path in paths) {
      mti.UpdateCaseCopyCount(path.CaseId, -1);
    }

    // Create a list of alternatives
    List<LiteralExpr> ifBlockLiterals = new List<LiteralExpr>();
    foreach (var path in paths) {
      var head = GetPatternHead(path);
      var lit = GetLiteralExpressionFromPattern(head);

      if (lit != null) {
        lit.Type = matchees.Head.Type;
      }

      if (lit != null && !ifBlockLiterals.Exists(x => object.Equals(x.Value, lit.Value))) {
        ifBlockLiterals.Add(lit);
      }
    }

    var ifBlocks = new List<(LiteralExpr conditionValue, CaseBody block)>();
    // For each possible alternatives, filter potential cases and recur
    foreach (var ifBlockLiteral in ifBlockLiterals) {
      var pathsForLiteral = new List<PatternPath>();
      foreach (var path in paths) {
        var (head, tail) = SplitPath(path);
        var lit = GetLiteralExpressionFromPattern(head);

        var newPath = head is IdPattern idPattern
          ? LetBindNonWildCard(idPattern, ifBlockLiteral, tail)
          : tail;

        if (lit != null) {
          // if pattern matches the current alternative, add it to the path for this case, otherwise ignore it
          if (Equals(lit.Value, ifBlockLiteral.Value)) {
            mti.UpdateCaseCopyCount(tail.CaseId, 1);
            pathsForLiteral.Add(newPath);
          }
        } else if (head is IdPattern _) {
          // pattern is a bound variable, clone and let-bind the Lit
          mti.UpdateCaseCopyCount(tail.CaseId, 1);
          pathsForLiteral.Add(newPath);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      }
      var blockContext = context.FillHole(new LitCtx(ifBlockLiteral));

      var block = CompilePatternPaths(mti, blockContext, matchees.Tail, pathsForLiteral);
      ifBlocks.Add((ifBlockLiteral, block));
    }
    // Create a default case
    var defaultPaths = new List<PatternPath>();
    foreach (var path in paths) {
      var (head, tail) = SplitPath(path);
      if (head is IdPattern idPattern && idPattern.ResolvedLit == null && idPattern.Arguments == null) {
        var newPath = LetBindNonWildCard(idPattern, matchees.Head, tail);
        mti.UpdateCaseCopyCount(tail.CaseId, 1);
        defaultPaths.Add(newPath);
      }
    }
    // defaultPaths.Count check is to avoid adding "missing paths" when default is not present
    var defaultBlock = defaultPaths.Count == 0 ? null : CompilePatternPaths(mti, context.AbstractHole(), matchees.Tail, defaultPaths);

    return CreateIfElseIfChain(mti, context, matchees.Head, ifBlocks, defaultBlock);
  }

  private static LiteralExpr GetLiteralExpressionFromPattern(ExtendedPattern head) {
    LiteralExpr lit = null;
    if (head is LitPattern litPattern) {
      lit = litPattern.OptimisticallyDesugaredLit;
    } else if (head is IdPattern id && id.ResolvedLit != null) {
      lit = id.ResolvedLit;
    }

    return lit;
  }

  // Assumes that all SyntaxContainers in blocks and def are of the same subclass
  private CaseBody CreateIfElseIfChain(MatchCompilationState mti, MatchingContext context, Expression matchee,
    List<(LiteralExpr, CaseBody)> blocks, CaseBody defaultBlock) {

    if (blocks.Count == 0) {
      if (defaultBlock?.Node is Statement stmt) {
        // Ensures the statements are wrapped in braces
        return new CaseBody(null, BlockStmtOfCStmt(stmt.RangeToken, stmt));
      }

      return defaultBlock;
    }

    var currBlock = blocks.First();
    blocks = blocks.Skip(1).ToList();

    var tok = matchee.Tok;
    var range = matchee.Tok.ToRange();
    var guard = new BinaryExpr(mti.Match.Tok, BinaryExpr.Opcode.Eq, matchee, currBlock.Item1) {
      ResolvedOp = BinaryExpr.ResolvedOpcode.EqCommon,
      Type = Type.Bool
    };

    var contextStr = context.FillHole(new IdCtx($"c: {matchee.Type}", new List<MatchingContext>())).AbstractAllHoles().ToString();
    var errorMessage = mti.Match.Source.Type.AsDatatype == null
      ? $"missing case in match {mti.Match.MatchTypeName}: not all possibilities for selector of type {matchee.Type} have been covered"
      : $"missing case in match {mti.Match.MatchTypeName}: {contextStr} (not all possibilities for constant 'c' have been covered)";

    var assertGuard = AssertStmt.CreateErrorAssert(mti.Match, errorMessage, guard);
    var elseCase = CreateIfElseIfChain(mti, context, matchee, blocks, defaultBlock);

    if (currBlock.Item2.Node is Expression expression) {
      if (elseCase is null) {
        // handle an empty default
        // assert guard; item2.Body
        var result = new StmtExpr(tok, assertGuard, expression);
        result.Type = ((NestedMatchExpr)mti.Match).Type;
        return new CaseBody(null, result);
      } else {
        var els = (Expression)elseCase.Node;
        var result = new ITEExpr(tok, false, guard, expression, els);
        result.Type = ((NestedMatchExpr)mti.Match).Type;
        return new CaseBody(null, result);
      }
    }

    if (currBlock.Item2.Node is Statement statement) {
      var item2 = BlockStmtOfCStmt(range, statement);
      if (elseCase is null) {
        // handle an empty default
        // assert guard; item2.Body
        var body = new List<Statement>();
        body.Add(assertGuard);
        body.AddRange(item2.Body);
        return new CaseBody(null, new BlockStmt(range, body));
      } else {
        var els = (Statement)elseCase.Node;
        return new CaseBody(null, new IfStmt(range, false, guard, item2, els));
      }
    }

    throw new cce.UnreachableException();
  }

  record CaseBody(IToken Tok, Node Node, Attributes Attributes = null);

  private CaseBody PackBody(IToken tok, PatternPath path) {
    if (path is StmtPatternPath br) {
      return new CaseBody(tok, new BlockStmt(tok.ToRange(), br.Body.ToList()), br.Attributes);
    }

    if (path is ExprPatternPath) {
      return new CaseBody(tok, ((ExprPatternPath)path).Body, ((ExprPatternPath)path).Attributes);
    }

    Contract.Assert(false); throw new cce.UnreachableException();
  }

  private List<Statement> UnboxStmt(Statement statement) {
    if (statement is BlockStmt block) {
      return block.Body;
    }

    return new List<Statement>() { statement };
  }

  private BlockStmt BlockStmtOfCStmt(RangeToken rangeToken, Statement stmt) {
    if (stmt is BlockStmt) {
      return (BlockStmt)stmt;
    }

    var stmts = new List<Statement>();
    stmts.Add(stmt);
    return new BlockStmt(rangeToken, stmts);
  }

  private class MatchCompilationState {
    public INestedMatch Match { get; }
    public readonly IToken[] CaseTok;
    public readonly int[] CaseCopyCount;

    public IToken Tok => Match switch {
      NestedMatchExpr matchExpr => matchExpr.tok,
      NestedMatchStmt matchStmt => matchStmt.Tok,
      _ => throw new ArgumentOutOfRangeException(nameof(Match))
    };

    public readonly ResolutionContext CodeContext;
    public Attributes Attributes;

    public MatchCompilationState(INestedMatch match, IReadOnlyList<NestedMatchCase> flattenedCases, ResolutionContext codeContext,
      Attributes attrs = null) {
      this.Match = match;
      this.CaseTok = flattenedCases.Select(c => c.Tok).ToArray();
      this.CaseCopyCount = new int[flattenedCases.Count];
      Array.Fill(CaseCopyCount, 1);
      this.CodeContext = codeContext;
      this.Attributes = attrs;
    }

    public void UpdateCaseCopyCount(int caseId, int delta) {
      CaseCopyCount[caseId] += delta;
    }
  }

  private abstract record PatternPath(IToken Tok, int CaseId, List<ExtendedPattern> Patterns) {
  }

  private record StmtPatternPath(IToken Tok, int CaseId, List<ExtendedPattern> Patterns,
    IReadOnlyList<Statement> Body, Attributes Attributes) : PatternPath(Tok, CaseId, Patterns) {

    public StmtPatternPath(int caseId, NestedMatchCaseStmt x, Attributes attrs = null) :
      this(x.Tok, caseId, new List<ExtendedPattern>() { x.Pat },
      new List<Statement>(x.Body), attrs) {
      Contract.Requires(!(x.Pat is DisjunctivePattern)); // No nested or patterns
    }

    public override string ToString() {
      var bodyStr = "";
      foreach (var stmt in this.Body) {
        bodyStr += string.Format("{1}{0};\n", Printer.StatementToString(DafnyOptions.DefaultImmutableOptions, stmt), "\t");
      }
      return string.Format("\t> id: {0}\n\t> patterns: <{1}>\n\t-> body:\n{2} \n", this.CaseId, String.Join(",", this.Patterns.ConvertAll(x => x.ToString())), bodyStr);
    }
  }

  private record ExprPatternPath(IToken Tok, int CaseId, List<ExtendedPattern> Patterns,
    Expression Body, Attributes Attributes) : PatternPath(Tok, CaseId, Patterns) {

    public ExprPatternPath(int caseId, NestedMatchCaseExpr x, Attributes attrs = null) : this(x.Tok, caseId,
      new List<ExtendedPattern>() { x.Pat }, x.Body, attrs) {
    }

    public override string ToString() {
      return
        $"\t> id: {this.CaseId}\n\t-> patterns: <{String.Join(",", this.Patterns.ConvertAll(x => x.ToString()))}>\n\t-> body: {Printer.ExprToString(DafnyOptions.DefaultImmutableOptions, this.Body)}";
    }
  }

  private static (ExtendedPattern, PatternPath) SplitPath(PatternPath path) {
    return (GetPatternHead(path), DropPatternHead(path));
  }

  private static ExtendedPattern GetPatternHead(PatternPath path) {
    return path.Patterns.First();
  }

  private static PatternPath DropPatternHead(PatternPath path) {
    return path switch {
      ExprPatternPath expr => new ExprPatternPath(expr.Tok, expr.CaseId, expr.Patterns.Skip(1).ToList(), expr.Body,
        expr.Attributes),
      StmtPatternPath stmt => new StmtPatternPath(stmt.Tok, stmt.CaseId, stmt.Patterns.Skip(1).ToList(), stmt.Body,
        stmt.Attributes),
      _ => throw new ArgumentOutOfRangeException(nameof(path))
    };
  }

  // let-bind a variable of name "name" and type "type" as "expr" on the body of "path"
  private PatternPath LetBind(IdPattern var, Expression genExpr, PatternPath bodyPath) {
    var name = var.Id;
    var type = var.Type ?? new InferredTypeProxy();
    var isGhost = var.IsGhost;

    // if the expression is a generated IdentifierExpr, replace its token by the path's
    Expression expr = genExpr;
    if (genExpr is IdentifierExpr idExpr) {
      if (idExpr.Name.StartsWith("_")) {
        expr = new IdentifierExpr(var.Tok, idExpr.Var);
      }
    }
    if (bodyPath is StmtPatternPath stmtPath) {
      if (stmtPath.Body.Count <= 0) {
        return stmtPath;
      }

      var caseLocal = new LocalVariable(var.RangeToken, name, type, isGhost);
      caseLocal.type = type;
      var casePattern = new CasePattern<LocalVariable>(caseLocal.RangeToken.EndToken, caseLocal);
      casePattern.AssembleExpr(new List<Type>());
      var caseLet = new VarDeclPattern(caseLocal.RangeToken, casePattern, expr, false);
      caseLet.IsGhost = isGhost;

      var substitutions = new Dictionary<IVariable, Expression>() {
        { var.BoundVar, new IdentifierExpr(var.BoundVar.Tok, caseLocal)}
      };

      var cloner = new SubstitutingCloner(substitutions, true);
      var clonedBody = stmtPath.Body.Select(s => cloner.CloneStmt(s)).ToList();

      return new StmtPatternPath(stmtPath.Tok, stmtPath.CaseId, stmtPath.Patterns, new[] { caseLet }.Concat(clonedBody).ToList(), stmtPath.Attributes);
    }

    if (bodyPath is ExprPatternPath exprPath) {
      var cBVar = (BoundVar)var.BoundVar;
      cBVar.IsGhost = isGhost;
      var cPat = new CasePattern<BoundVar>(cBVar.Tok, cBVar);
      cPat.AssembleExpr(new List<Type>());
      var cPats = new List<CasePattern<BoundVar>>();
      cPats.Add(cPat);
      var exprs = new List<Expression>();
      exprs.Add(expr);

      var letExpr = new LetExpr(cBVar.tok, cPats, exprs, exprPath.Body, true);
      letExpr.Type = exprPath.Body.Type;
      return new ExprPatternPath(exprPath.Tok, exprPath.CaseId, exprPath.Patterns, letExpr, exprPath.Attributes);
    } else {
      throw new InvalidOperationException();
    }
  }

  // If cp is not a wildcard, replace path.Body with let cp = expr in path.Body
  // Otherwise do nothing
  private PatternPath LetBindNonWildCard(IdPattern var, Expression expr, PatternPath bodyPath) {
    if (!var.IsWildcardPattern) {
      return LetBind(var, expr, bodyPath);
    }

    return bodyPath;
  }
}
