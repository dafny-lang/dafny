#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using DafnyCore;
using Microsoft.Dafny.Auditor;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class Function : MethodOrFunction, TypeParameter.ParentType, ICallable, ICanFormat, IHasDocstring,
  ICanAutoRevealDependencies, ICanVerify {
  public override string WhatKind => "function";

  public override bool HasStaticKeyword { get; }


  public string GetFunctionDeclarationKeywords(DafnyOptions options) {
    string k;
    if (this is TwoStateFunction || this is ExtremePredicate || this.ByMethodBody != null) {
      k = WhatKind;
    } else if (this is PrefixPredicate) {
      k = "predicate";
    } else if (options.FunctionSyntax == FunctionSyntaxOptions.ExperimentalPredicateAlwaysGhost &&
               (this is Predicate || !IsGhost)) {
      k = WhatKind;
    } else if (options.FunctionSyntax != FunctionSyntaxOptions.Version4 && !IsGhost) {
      k = WhatKind + " method";
    } else if (options.FunctionSyntax != FunctionSyntaxOptions.Version3 && IsGhost) {
      k = "ghost " + WhatKind;
    } else {
      k = WhatKind;
    }

    // If this function is opaque due to the opaque keyword, include it.
    k = (IsOpaque && !Attributes.Contains(Attributes, "opaque")) ? "opaque " + k : k;
    return HasStaticKeyword ? "static " + k : k;
  }

  public override bool IsOpaque { get; }

  public bool IsMadeImplicitlyOpaque(DafnyOptions options) {
    return
       !IsOpaque &&
       !Attributes.Contains(Attributes, "opaque") &&
       options.Get(CommonOptionBag.DefaultFunctionOpacity) != CommonOptionBag.DefaultFunctionOpacityOptions.Transparent
       && this is not ExtremePredicate
       && this is not PrefixPredicate
       && Name != "reads" && Name != "requires"
       && !Attributes.Contains(this.Attributes, "transparent");
  }

  public override bool CanBeRevealed() {
    return true;
  }

  public override bool HasPostcondition =>
    Ens.Count > 0 || ResultType.AsSubsetType is not null;

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var a in base.Assumptions(this)) {
      yield return a;
    }

    if (Body is null && HasPostcondition && EnclosingClass.EnclosingModuleDefinition.ModuleKind == ModuleKindEnum.Concrete && !HasExternAttribute && !HasAxiomAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.NoBody(IsGhost));
    }

    if (HasExternAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.ExternFunction);
      if (HasPostcondition && !HasAxiomAttribute) {
        yield return new Assumption(this, Origin, AssumptionDescription.ExternWithPostcondition);
      }
    }

    if (HasExternAttribute && HasPrecondition && !HasAxiomAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.ExternWithPrecondition);
    }

    foreach (var c in this.Descendants()) {
      foreach (var a in (c as Node)?.Assumptions(this) ?? []) {
        yield return a;
      }
    }

  }

  [FilledInDuringResolution] public bool IsRecursive;

  [FilledInDuringResolution]
  public TailStatus
    TailRecursion =
      TailStatus.NotTailRecursive; // NotTailRecursive = no tail recursion; TriviallyTailRecursive is never used here

  public bool IsTailRecursive => TailRecursion != TailStatus.NotTailRecursive;
  public bool IsAccumulatorTailRecursive => IsTailRecursive && TailRecursion != TailStatus.TailRecursive;
  [FilledInDuringResolution] public bool IsFueled; // if anyone tries to adjust this function's fuel
  public Formal? Result;
  public PreType? ResultPreType;
  public Type ResultType;
  public Type OriginalResultTypeWithRenamings() {
    if (OverriddenFunction == null) {
      return ResultType;
    }

    Contract.Assert(TypeArgs.Count == OverriddenFunction.TypeArgs.Count);
    var renamings = new Dictionary<TypeParameter, Type>();
    for (var i = 0; i < TypeArgs.Count; i++) {
      renamings.Add(OverriddenFunction.TypeArgs[i], new UserDefinedType(Origin, TypeArgs[i]));
    }
    return OverriddenFunction.ResultType.Subst(renamings);

  }
  public Expression? Body; // an extended expression; Body is after construction, except for any kind of rewrite that may take place around the time of resolution
  public IOrigin? ByMethodTok; // null iff ByMethodBody is null
  public BlockStmt? ByMethodBody;
  [FilledInDuringResolution] public Method? ByMethodDecl; // if ByMethodBody is non-null
  public Function? OverriddenFunction;
  public Function Original => OverriddenFunction == null ? this : OverriddenFunction.Original;
  public override bool IsOverrideThatAddsBody => base.IsOverrideThatAddsBody && Body != null;
  public bool AllowsAllocation => true;
  public bool containsQuantifier;

  public bool ContainsQuantifier {
    set { containsQuantifier = value; }
    get { return containsQuantifier; }
  }

  public enum TailStatus {
    TriviallyTailRecursive, // contains no recursive calls (in non-ghost expressions)
    TailRecursive, // all recursive calls (in non-ghost expressions) are tail calls
    NotTailRecursive, // contains some non-ghost recursive call outside of a tail-call position
    // E + F or F + E, where E has no tail call and F is a tail call
    Accumulate_Add,
    AccumulateRight_Sub,
    Accumulate_Mul,
    Accumulate_SetUnion,
    AccumulateRight_SetDifference,
    Accumulate_MultiSetUnion,
    AccumulateRight_MultiSetDifference,
    AccumulateLeft_Concat,
    AccumulateRight_Concat,
  }

  public override IEnumerable<INode> Children => Util.IgnoreNulls(ByMethodBody!).
    Concat<Node>(TypeArgs).
    Concat<Node>(Reads.Expressions!).
    Concat<Node>(Req).
    Concat(Ens.Select(e => e.E)).
    Concat(Decreases.Expressions!).
    Concat(Ins).
    Concat(Result != null ? [Result] : new List<Node>()).
    Concat(new List<Node>() { ResultType }).
    Concat(Body == null ? Enumerable.Empty<Node>() : new[] { Body });

  public override IEnumerable<INode> PreResolveChildren =>
    TypeArgs.
    Concat<Node>(Reads.Expressions).
    Concat<Node>(Req).
    Concat(Ens).
    Concat(Decreases.Expressions!.Where(expression => expression is not AutoGeneratedExpression)).
    Concat(Ins).Concat(ResultType != null && ResultType.Origin.line > 0 ? [ResultType] : new List<Node>()).
    Concat(Body == null ? Enumerable.Empty<Node>() : new[] { Body }).
    Concat(ByMethodBody == null ? Enumerable.Empty<Node>() : new[] { ByMethodBody });

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var formal in Ins.Where(f => f.DefaultValue != null)) {
        yield return formal.DefaultValue!;
      }
      foreach (var e in Req) {
        yield return e.E;
      }
      foreach (var e in Reads.Expressions!) {
        yield return e.E;
      }
      foreach (var e in Ens) {
        yield return e.E;
      }
      foreach (var e in Decreases.Expressions!) {
        yield return e;
      }
      if (Body != null) {
        yield return Body;
      }
    }
  }

  public Type GetMemberType(ArrowTypeDecl atd) {
    Contract.Requires(atd.Arity == Ins.Count);

    // Note, the following returned type can contain type parameters from the function and its enclosing class
    return new ArrowType(Origin, atd, Ins.ConvertAll(f => f.Type), ResultType);
  }

  public bool AllowsNontermination {
    get {
      return Contract.Exists(Decreases.Expressions!, e => e is WildcardExpr);
    }
  }

  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;

  /// <summary>
  /// The "AllCalls" field is used for non-ExtremePredicate, non-PrefixPredicate functions only (so its value should not be relied upon for ExtremePredicate and PrefixPredicate functions).
  /// It records all function calls made by the Function, including calls made in the body as well as in the specification.
  /// The field is filled in during resolution (and used toward the end of resolution, to attach a helpful "decreases" prefix to functions in clusters
  /// with co-recursive calls.
  /// </summary>
  public List<FunctionCallExpr> AllCalls = [];
  public enum CoCallClusterInvolvement {
    None,  // the SCC containing the function does not involve any co-recursive calls
    IsMutuallyRecursiveTarget,  // the SCC contains co-recursive calls, and this function is the target of some non-self recursive call
    CoRecursiveTargetAllTheWay,  // the SCC contains co-recursive calls, and this function is the target only of self-recursive calls and co-recursive calls
  }
  public CoCallClusterInvolvement CoClusterTarget = CoCallClusterInvolvement.None;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Cce.NonNullElements(TypeArgs));
    Contract.Invariant(Cce.NonNullElements(Ins));
    Contract.Invariant(ResultType != null);
    Contract.Invariant(Cce.NonNullElements(Req));
    Contract.Invariant(Reads != null);
    Contract.Invariant(Cce.NonNullElements(Ens));
    Contract.Invariant(Decreases != null);
  }

  [SyntaxConstructor]
  public Function(IOrigin origin, Name nameNode, bool hasStaticKeyword, bool isGhost, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> ins, Formal? result, Type resultType,
    List<AttributedExpression> req, Specification<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression? body, IOrigin? byMethodTok, BlockStmt? byMethodBody,
    Attributes? attributes, IOrigin? signatureEllipsis)
    : base(origin, nameNode, isGhost, attributes, signatureEllipsis, typeArgs, ins, req, ens, reads, decreases) {

    Contract.Requires(byMethodBody == null || (!isGhost && body != null)); // function-by-method has a ghost expr and non-ghost stmt, but to callers appears like a functiion-method
    this.IsFueled = false;  // Defaults to false.  Only set to true if someone mentions this function in a fuel annotation
    this.Result = result;
    this.ResultType = result != null ? result.Type : resultType;
    this.Body = body;
    this.ByMethodTok = byMethodTok;
    this.ByMethodBody = byMethodBody;
    this.IsOpaque = isOpaque || Attributes.Contains(attributes, "opaque");
    HasStaticKeyword = hasStaticKeyword;

    if (attributes == null) {
      return;
    }

    var args = Attributes.FindExpressions(attributes, "fuel");
    if (args == null) {
      return;
    }

    if (args.Count == 1) {
      if (args[0] is LiteralExpr { Value: BigInteger }) {
        IsFueled = true;
      }
    } else if (args.Count == 2) {
      if (args[0] is LiteralExpr { Value: BigInteger } && args[1] is LiteralExpr { Value: BigInteger }) {
        IsFueled = true;
      }
    }
  }

  public override bool IsRefining => SignatureEllipsis != null;

  bool ICodeContext.IsGhost { get { return IsGhost; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return Ins; } }
  string ICallable.NameRelativeToModule {
    get {
      if (EnclosingClass is DefaultClassDecl) {
        return Name;
      } else {
        return EnclosingClass.Name + "." + Name;
      }
    }
  }
  Specification<Expression> ICallable.Decreases { get { return Decreases; } }
  bool _inferredDecr;
  bool ICallable.InferredDecreases {
    set { _inferredDecr = value; }
    get { return _inferredDecr; }
  }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return EnclosingClass.EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }

  [Pure]
  public bool IsFuelAware() { return IsRecursive || IsFueled || (OverriddenFunction != null && OverriddenFunction.IsFuelAware()); }
  public virtual bool ReadsHeap { get { return Reads.Expressions!.Count != 0; } }

  public static Option<string> FunctionSyntaxOption = new("--function-syntax",
    () => "4",
    @"
The syntax for functions changed from Dafny version 3 to version 4. This switch controls access to the new syntax, and also provides a mode to help with migration.

3 - Compiled functions are written `function method` and `predicate method`. Ghost functions are written `function` and `predicate`.
4 - Compiled functions are written `function` and `predicate`. Ghost functions are written `ghost function` and `ghost predicate`.
migration3to4 - Compiled functions are written `function method` and `predicate method`. Ghost functions are written `ghost function` and `ghost predicate`. To migrate from version 3 to version 4, use this flag on your version 3 program. This will give flag all occurrences of `function` and `predicate` as parsing errors. These are ghost functions, so change those into the new syntax `ghost function` and `ghost predicate`. Then, start using --functionSyntax:4. This will flag all occurrences of `function method` and `predicate method` as parsing errors. So, change those to just `function` and `predicate`. Now, your program uses version 4 syntax and has the exact same meaning as your previous version 3 program.
experimentalDefaultGhost - Like migration3to4, but allow `function` and `predicate` as alternatives to declaring ghost functions and predicates, respectively.
experimentalDefaultCompiled - Like migration3to4, but allow `function` and `predicate` as alternatives to declaring compiled
    functions and predicates, respectively.
experimentalPredicateAlwaysGhost - Compiled functions are written `function`. Ghost functions are written `ghost function`. Predicates are always ghost and are written `predicate`."
      .TrimStart()
  ) {
    ArgumentHelpName = "version",
  };

  static Function() {
    var functionSyntaxOptionsMap = new Dictionary<string, FunctionSyntaxOptions> {
      { "3", FunctionSyntaxOptions.Version3 },
      { "4", FunctionSyntaxOptions.Version4 },
      { "migration3to4", FunctionSyntaxOptions.Migration3To4 },
      { "experimentalDefaultGhost", FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsGhost },
      { "experimentalDefaultCompiled", FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsCompiled },
      { "experimentalPredicateAlwaysGhost", FunctionSyntaxOptions.ExperimentalPredicateAlwaysGhost },
    };
    FunctionSyntaxOption = FunctionSyntaxOption.FromAmong(functionSyntaxOptionsMap.Keys.ToArray());
    DafnyOptions.RegisterLegacyBinding(FunctionSyntaxOption, (options, value) => {
      options.FunctionSyntax = functionSyntaxOptionsMap[value];
    });
    OptionRegistry.RegisterOption(FunctionSyntaxOption, OptionScope.Module);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    if (BodyStartTok.line > 0) {
      formatter.SetDelimiterIndentedRegions(BodyStartTok, indentBefore);
    }
    Attributes.SetIndents(Attributes, indentBefore, formatter);
    formatter.SetFormalsIndentation(Ins);
    if (Result is { } outFormal) {
      formatter.SetTypeIndentation(outFormal.SafeSyntacticType);
    }

    foreach (var req in Req) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var frame in Reads.Expressions!) {
      formatter.SetFrameExpressionIndentation(frame, indentBefore + formatter.SpaceTab);
    }

    foreach (var ens in Ens) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    foreach (var dec in Decreases.Expressions!) {
      formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
    }

    if (ByMethodBody is { } byMethodBody) {
      formatter.SetDelimiterIndentedRegions(byMethodBody.StartToken, indentBefore);
      formatter.SetClosingIndentedRegion(byMethodBody.EndToken, indentBefore);
      formatter.SetStatementIndentation(byMethodBody);
    }

    formatter.SetExpressionIndentation(Body);
    return true;
  }

  protected override bool Bodyless => Body == null;
  protected override string TypeName => "function";

  public void ResolveNewOrOldPart(INewOrOldResolver resolver) {
    ResolveMethodOrFunction(resolver);
  }

  /// <summary>
  /// Assumes type parameters have already been pushed
  /// </summary>
  public override void Resolve(ModuleResolver resolver) {
    Contract.Requires(this != null);
    Contract.Requires(resolver.AllTypeConstraints.Count == 0);
    Contract.Ensures(resolver.AllTypeConstraints.Count == 0);

    ResolveNewOrOldPart(resolver);

    // make note of the warnShadowing attribute
    bool warnShadowingOption = resolver.Options.WarnShadowing;  // save the original warnShadowing value
    bool warnShadowing = true;
    if (Attributes.ContainsBool(Attributes, "warnShadowing", ref warnShadowing)) {
      resolver.Options.WarnShadowing = warnShadowing;  // set the value according to the attribute
    }

    resolver.scope.PushMarker();
    if (IsStatic) {
      resolver.scope.AllowInstance = false;
    }

    foreach (Formal p in Ins) {
      resolver.scope.Push(p.Name, p);
    }

    resolver.ResolveParameterDefaultValues(Ins, ResolutionContext.FromCodeContext(this));

    var contractContext = new ResolutionContext(this, this is TwoStateFunction);
    foreach (var req in Req) {
      resolver.ResolveAttributes(req, contractContext);
      Expression r = req.E;
      resolver.ResolveExpression(r, contractContext);
      Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
      resolver.ConstrainTypeExprBool(r, "Precondition must be a boolean (got {0})");
    }
    resolver.ResolveAttributes(Reads, contractContext);
    foreach (FrameExpression fr in Reads.Expressions!) {
      resolver.ResolveFrameExpressionTopLevel(fr, FrameExpressionUse.Reads, this);
    }

    resolver.scope.PushMarker();
    if (Result != null) {
      resolver.scope.Push(Result.Name, Result);  // function return only visible in post-conditions (and in function attributes)
    }
    foreach (AttributedExpression e in Ens) {
      Expression r = e.E;
      resolver.ResolveAttributes(e, contractContext);
      resolver.ResolveExpression(r, contractContext with { InFunctionPostcondition = true });
      Contract.Assert(r.Type != null);  // follows from postcondition of ResolveExpression
      resolver.ConstrainTypeExprBool(r, "Postcondition must be a boolean (got {0})");
    }
    resolver.scope.PopMarker(); // function result name

    resolver.ResolveAttributes(Decreases, contractContext);
    foreach (Expression r in Decreases.Expressions!) {
      resolver.ResolveExpression(r, contractContext);
      // any type is fine
    }
    resolver.SolveAllTypeConstraints(); // solve type constraints in the specification

    if (Body != null) {

      resolver.DominatingStatementLabels.PushMarker();
      foreach (var req in Req) {
        if (req.Label != null) {
          if (resolver.DominatingStatementLabels.Find(req.Label.Name) != null) {
            resolver.reporter.Error(MessageSource.Resolver, req.Label.Tok, "assert label shadows a dominating label");
          } else {
            var rr = resolver.DominatingStatementLabels.Push(req.Label.Name, req.Label);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
      }
      resolver.ResolveExpression(Body, new ResolutionContext(this, this is TwoStateFunction));
      Contract.Assert(Body.Type != null);  // follows from postcondition of ResolveExpression
      resolver.AddAssignableConstraint(Origin, ResultType, Body.Type, "Function body type mismatch (expected {0}, got {1})");
      resolver.SolveAllTypeConstraints();
      resolver.DominatingStatementLabels.PopMarker();
    }

    resolver.scope.PushMarker();
    if (Result != null) {
      resolver.scope.Push(Result.Name, Result);  // function return only visible in post-conditions (and in function attributes)
    }
    resolver.ResolveAttributes(this, contractContext, true);
    resolver.scope.PopMarker(); // function result name

    resolver.scope.PopMarker(); // formals

    if (ByMethodBody != null) {
      Contract.Assert(Body != null && !IsGhost); // assured by the parser and other callers of the Function constructor
      var method = ByMethodDecl;
      if (method != null) {
        method.Resolve(resolver);
      } else {
        // method should have been filled in by now,
        // unless there was a function by method and a method of the same name
        // but then this error must have been reported.
        Contract.Assert(resolver.Reporter.HasErrors);
      }
    }

    resolver.Options.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
  }

  public string? GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    // Comments after the type, but before the clauses
    var endTokenDefinition =
      OwnedTokens.LastOrDefault(token => token.val == ")");
    if (endTokenDefinition != null && endTokenDefinition.pos < ResultType.EndToken.pos) {
      endTokenDefinition = ResultType.EndToken;
    }
    var tentativeTrivia = "";
    if (endTokenDefinition != null) {
      if (endTokenDefinition.pos < this.EndToken.pos) { // All comments are docstring
        tentativeTrivia = (endTokenDefinition.TrailingTrivia + endTokenDefinition.Next.LeadingTrivia).Trim();
      } else {
        // Comments at the end of bodiless functions
        tentativeTrivia = endTokenDefinition.TrailingTrivia.Trim();
      }
      if (tentativeTrivia != "") {
        return tentativeTrivia;
      }
    }

    tentativeTrivia = EndToken.TrailingTrivia.Trim();
    if (tentativeTrivia != "") {
      return tentativeTrivia;
    }

    return null;
  }

  public override SymbolKind? Kind => SymbolKind.Function;
  public bool ShouldVerify => true; // This could be made more accurate
  public ModuleDefinition ContainingModule => EnclosingClass.EnclosingModuleDefinition;
  public override string GetDescription(DafnyOptions options) {
    var formals = string.Join(", ", Ins.Select(f => f.AsText()));
    var resultType = ResultType.TypeName(options, null, false);
    return $"{WhatKind} {AstExtensions.GetMemberQualification(this)}{Name}({formals}): {resultType}";
  }

  public void AutoRevealDependencies(AutoRevealFunctionDependencies rewriter, DafnyOptions options,
    ErrorReporter reporter) {
    if (Body is null) {
      return;
    }

    if (ByMethodDecl is not null) {
      ByMethodDecl.AutoRevealDependencies(rewriter, options, reporter);
    }

    object? autoRevealDepsVal = null;
    bool autoRevealDeps = Attributes.ContainsMatchingValue(Attributes, "autoRevealDependencies",
      ref autoRevealDepsVal, new HashSet<Attributes.MatchingValueOption> {
        Attributes.MatchingValueOption.Bool,
        Attributes.MatchingValueOption.Int
      }, s => reporter.Message(MessageSource.Rewriter, ErrorLevel.Error, Origin, s));

    // Default behavior is reveal all dependencies
    int autoRevealDepth = int.MaxValue;

    if (autoRevealDeps) {
      if (autoRevealDepsVal is false) {
        autoRevealDepth = 0;
      } else if (autoRevealDepsVal is BigInteger i) {
        autoRevealDepth = (int)i;
      }
    }

    var currentClass = EnclosingClass;
    List<AutoRevealFunctionDependencies.RevealStmtWithDepth> addedReveals = [];

    foreach (var func in rewriter.GetEnumerator(this, currentClass, SubExpressions)) {
      var revealStmt =
        AutoRevealFunctionDependencies.BuildRevealStmt(func.Function, Origin, EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(new AutoRevealFunctionDependencies.RevealStmtWithDepth(revealStmt, func.Depth));
      }
    }

    if (autoRevealDepth > 0) {
      Expression reqExpr = Expression.CreateBoolLiteral(Origin, true);

      var bodyExpr = Body;

      foreach (var revealStmt in addedReveals) {
        if (revealStmt.Depth <= autoRevealDepth) {
          bodyExpr = new StmtExpr(Origin, revealStmt.RevealStmt, bodyExpr) {
            Type = bodyExpr.Type
          };

          reqExpr = new StmtExpr(reqExpr.Origin, revealStmt.RevealStmt, reqExpr) {
            Type = Type.Bool
          };
        } else {
          break;
        }
      }

      Body = bodyExpr;

      if (Req.Any() || Ens.Any()) {
        Req.Insert(0, new AttributedExpression(reqExpr));
      }
    }

    if (addedReveals.Any()) {
      reporter.Message(MessageSource.Rewriter, ErrorLevel.Info, null, Origin,
        AutoRevealFunctionDependencies.GenerateMessage(addedReveals, autoRevealDepth));
    }
  }
  public string Designator => WhatKind;
}
