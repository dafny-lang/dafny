#nullable enable
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using DafnyCore.Options;
using Microsoft.Dafny.Auditor;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class MethodOrConstructor : MethodOrFunction, TypeParameter.ParentType,
  IMethodCodeContext, ICanFormat, IHasDocstring, IHasSymbolChildren, ICanAutoRevealDependencies, ICanVerify {
  public abstract List<Formal> Outs { get; }

  public static readonly Option<bool> ReadsClausesOnMethods = new("--reads-clauses-on-methods",
    "Allows reads clauses on methods (with a default of 'reads *') as well as functions."
  );

  static MethodOrConstructor() {
    DafnyOptions.RegisterLegacyUi(ReadsClausesOnMethods, DafnyOptions.ParseBoolean, "Language feature selection", "readsClausesOnMethods", @"
0 (default) - Reads clauses on methods are forbidden.
1 - Reads clauses on methods are permitted (with a default of 'reads *').".TrimStart(), defaultValue: false);
    OptionRegistry.RegisterGlobalOption(ReadsClausesOnMethods, OptionCompatibility.CheckOptionLocalImpliesLibrary);
  }

  public override IEnumerable<INode> Children => Util.IgnoreNulls<Node>(Body!, Decreases).
    Concat(Ins).Concat(Outs).Concat<Node>(TypeArgs).
    Concat(Req).Concat(Ens).Concat(Reads.Expressions!).Concat(Mod.Expressions!);

  public override IEnumerable<INode> PreResolveChildren => Children;
  public override string WhatKind => "method";
  public bool MustReverify;
  public bool IsEntryPoint = false;
  public readonly Specification<FrameExpression> Mod;
  [FilledInDuringResolution] public bool IsRecursive;
  [FilledInDuringResolution] public bool IsTailRecursive;
  [FilledInDuringResolution] public Function? FunctionFromWhichThisIsByMethodDecl;
  public readonly ISet<IVariable> AssignedAssumptionVariables = new HashSet<IVariable>();

  public Method? OverriddenMethod;
  public MethodOrConstructor Original => OverriddenMethod == null ? this : OverriddenMethod.Original;
  public override bool IsOverrideThatAddsBody => base.IsOverrideThatAddsBody && Body != null;

  public override bool HasPostcondition =>
    Ens.Count > 0
    // This check is incomplete, which is a bug
    || Outs.Any(f => f.Type.AsSubsetType is not null);

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var a in base.Assumptions(this)) {
      yield return a;
    }

    if (Body is null && HasPostcondition && EnclosingClass.EnclosingModuleDefinition.ModuleKind == ModuleKindEnum.Concrete && !HasExternAttribute && !HasAxiomAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.NoBody(IsGhost));
    }

    if (HasExternAttribute && HasPostcondition && !HasAxiomAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.ExternWithPostcondition);
    }

    if (HasExternAttribute && HasPrecondition && !HasAxiomAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.ExternWithPrecondition);
    }

    if (Attributes.Contains(Reads.Attributes, Attributes.AssumeConcurrentAttributeName)) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasAssumeConcurrentAttribute(false));
    }
    if (Attributes.Contains(Mod.Attributes, Attributes.AssumeConcurrentAttributeName)) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasAssumeConcurrentAttribute(true));
    }

    if (AllowsNontermination) {
      yield return new Assumption(this, Origin, AssumptionDescription.MayNotTerminate);
    }

    foreach (var c in this.Descendants()) {
      foreach (var a in (c as Node)?.Assumptions(this) ?? []) {
        yield return a;
      }
    }
  }

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
      foreach (var e in Mod.Expressions!) {
        yield return e.E;
      }
      foreach (var e in Ens) {
        yield return e.E;
      }
      foreach (var e in Decreases.Expressions!) {
        yield return e;
      }
    }
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TypeArgs));
    Contract.Invariant(cce.NonNullElements(Ins));
    Contract.Invariant(cce.NonNullElements(Outs));
    Contract.Invariant(cce.NonNullElements(Req));
    Contract.Invariant(Reads != null);
    Contract.Invariant(Mod != null);
    Contract.Invariant(cce.NonNullElements(Ens));
    Contract.Invariant(Decreases != null);
  }

  protected MethodOrConstructor(Cloner cloner, MethodOrConstructor original) : base(cloner, original) {
    this.Mod = cloner.CloneSpecFrameExpr(original.Mod);
  }

  [SyntaxConstructor]
  protected MethodOrConstructor(IOrigin origin, Name nameNode,
    Attributes? attributes,
    bool isGhost,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins,
    [Captured] List<AttributedExpression> req,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<FrameExpression> reads,
    [Captured] Specification<Expression> decreases,
    [Captured] Specification<FrameExpression> mod,
    IOrigin? signatureEllipsis)
    : base(origin, nameNode, isGhost, attributes, signatureEllipsis, typeArgs, ins, req, ens, reads, decreases) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ins));
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(reads != null);
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
    this.Mod = mod;
    MustReverify = false;
  }

  public override bool IsRefining => SignatureEllipsis != null;

  bool ICodeContext.IsGhost { get { return this.IsGhost; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return this.Ins; } }
  List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
  Specification<FrameExpression> IMethodCodeContext.Modifies { get { return Mod; } }
  string ICallable.NameRelativeToModule {
    get {
      if (EnclosingClass is DefaultClassDecl) {
        return Name;
      } else {
        return EnclosingClass.Name + "." + Name;
      }
    }
  }
  Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
  bool _inferredDecr;
  bool ICallable.InferredDecreases {
    set { _inferredDecr = value; }
    get { return _inferredDecr; }
  }

  public virtual bool AllowsAllocation => true;

  ModuleDefinition IASTVisitorContext.EnclosingModule {
    get {
      Contract.Assert(this.EnclosingClass != null);  // this getter is supposed to be called only after signature-resolution is complete
      return this.EnclosingClass.EnclosingModuleDefinition;
    }
  }
  bool ICodeContext.MustReverify { get { return this.MustReverify; } }
  public bool AllowsNontermination {
    get {
      return Contract.Exists(Decreases.Expressions!, e => e is WildcardExpr);
    }
  }

  CodeGenIdGenerator ICodeContext.CodeGenIdGenerator => CodeGenIdGenerator;

  public override string GetCompileName(DafnyOptions options) {
    var nm = base.GetCompileName(options);
    if (nm == Dafny.Compilers.SinglePassCodeGenerator.DefaultNameMain && IsStatic && !IsEntryPoint) {
      // for a static method that is named "Main" but is not a legal "Main" method,
      // change its name.
      nm = EnclosingClass.Name + "_" + nm;
    }

    return nm;
  }

  public bool IsLemmaLike => this is Lemma || this is TwoStateLemma || this is ExtremeLemma || this is PrefixLemma;

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    if (BodyStartTok.line > 0) {
      formatter.SetDelimiterIndentedRegions(BodyStartTok, indentBefore);
    }

    Attributes.SetIndents(Attributes, indentBefore, formatter);

    formatter.SetFormalsIndentation(Ins);
    formatter.SetFormalsIndentation(Outs);
    foreach (var req in Req) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var read in Reads.Expressions!) {
      formatter.SetFrameExpressionIndentation(read, indentBefore + formatter.SpaceTab);
    }

    foreach (var mod in Mod.Expressions!) {
      formatter.SetFrameExpressionIndentation(mod, indentBefore + formatter.SpaceTab);
    }

    foreach (var ens in Ens) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    foreach (var dec in Decreases.Expressions!) {
      formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
      formatter.SetExpressionIndentation(dec);
    }

    if (Body != null) {
      formatter.SetStatementIndentation(this.Body);
    }

    return true;
  }

  public abstract BlockLikeStmt? Body { get; }

  public abstract void SetBody(BlockLikeStmt newBody);

  protected override bool Bodyless => Body == null;
  protected override string TypeName => "method";

  /// <summary>
  /// Assumes type parameters have already been pushed
  /// </summary>
  public override void Resolve(ModuleResolver resolver) {
    Contract.Requires(this != null);
    Contract.Requires(resolver.AllTypeConstraints.Count == 0);
    Contract.Ensures(resolver.AllTypeConstraints.Count == 0);

    ResolveMethodOrFunction(resolver);

    try {
      resolver.currentMethod = this;

      // make note of the warnShadowing attribute
      bool warnShadowingOption = resolver.Options.WarnShadowing;  // save the original warnShadowing value
      bool warnShadowing = true;
      if (Attributes.ContainsBool(Attributes, "warnShadowing", ref warnShadowing)) {
        resolver.Options.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      resolver.scope.PushMarker();
      if (IsStatic || this is Constructor) {
        resolver.scope.AllowInstance = false;
      }
      foreach (Formal p in Ins) {
        resolver.scope.Push(p.Name, p);
      }

      var resolutionContext = new ResolutionContext(this, this is TwoStateLemma);
      resolver.ResolveParameterDefaultValues(Ins, resolutionContext);

      // Start resolving specification...
      foreach (AttributedExpression e in Req) {
        resolver.ResolveAttributes(e, resolutionContext);
        resolver.ResolveExpression(e.E, resolutionContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        resolver.ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      var context = new ResolutionContext(this, false);
      resolver.ResolveAttributes(Reads, context);
      foreach (FrameExpression fe in Reads.Expressions!) {
        resolver.ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Reads, this);
      }

      resolver.ResolveAttributes(Mod, context);
      foreach (FrameExpression fe in Mod.Expressions!) {
        resolver.ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Modifies, this);
      }

      resolver.ResolveAttributes(Decreases, context);
      foreach (Expression e in Decreases.Expressions!) {
        resolver.ResolveExpression(e, resolutionContext);
        // any type is fine
      }

      if (this is Constructor) {
        resolver.scope.PopMarker();
        // start the scope again, but this time allowing instance
        resolver.scope.PushMarker();
        foreach (Formal p in Ins) {
          resolver.scope.Push(p.Name, p);
        }
      }

      // Add out-parameters to a new scope that will also include the outermost-level locals of the body
      // Don't care about any duplication errors among the out-parameters, since they have already been reported
      resolver.scope.PushMarker();
      if (this is ExtremeLemma && Outs.Count != 0) {
        resolver.reporter.Error(MessageSource.Resolver, Outs[0].Origin, "{0}s are not allowed to have out-parameters", WhatKind);
      } else {
        foreach (Formal p in Outs) {
          resolver.scope.Push(p.Name, p);
        }
      }

      // ... continue resolving specification
      foreach (AttributedExpression e in Ens) {
        var ensuresContext = new ResolutionContext(this, true);
        resolver.ResolveAttributes(e, ensuresContext);
        resolver.ResolveExpression(e.E, ensuresContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        resolver.ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }

      resolver.SolveAllTypeConstraints(); // solve type constraints for specification

      // Resolve body
      if (Body != null) {
        if (this is ExtremeLemma com && com.PrefixLemma != null) {
          // The body may mentioned the implicitly declared parameter _k.  Throw it into the
          // scope before resolving the body.
          var k = com.PrefixLemma.Ins[0];
          resolver.scope.Push(k.Name, k);  // we expect no name conflict for _k
        }

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

        resolver.ResolveBlockStatement(Body, ResolutionContext.FromCodeContext(this));
        resolver.DominatingStatementLabels.PopMarker();
        resolver.SolveAllTypeConstraints();
      }

      // attributes are allowed to mention both in- and out-parameters (including the implicit _k, for greatest lemmas)
      resolver.ResolveAttributes(this, resolutionContext, true);

      resolver.Options.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
      resolver.scope.PopMarker();  // for the out-parameters and outermost-level locals
      resolver.scope.PopMarker();  // for the in-parameters

    }
    finally {
      resolver.currentMethod = null;
    }
  }

  public string? GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    Token? lastClosingParenthesis = null;
    foreach (var token in OwnedTokens) {
      if (token.val == ")") {
        lastClosingParenthesis = token;
      }
    }

    var tentativeTrivia = "";
    if (lastClosingParenthesis != null) {
      if (lastClosingParenthesis.pos < EndToken.pos) {
        tentativeTrivia = (lastClosingParenthesis.TrailingTrivia + lastClosingParenthesis.Next.LeadingTrivia).Trim();
      } else {
        tentativeTrivia = lastClosingParenthesis.TrailingTrivia.Trim();
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

  public override SymbolKind? Kind => SymbolKind.Method;
  public override string GetDescription(DafnyOptions options) {
    var qualifiedName = GetQualifiedName();
    var signatureWithoutReturn = $"{WhatKind} {qualifiedName}({string.Join(", ", Ins.Select(i => i.AsText()))})";
    if (Outs.Count == 0) {
      return signatureWithoutReturn;
    }
    return $"{signatureWithoutReturn} returns ({string.Join(", ", Outs.Select(o => o.AsText()))})";
  }

  protected virtual string GetQualifiedName() {
    return $"{AstExtensions.GetMemberQualification(this)}{Name}";
  }

  public IEnumerable<ISymbol> ChildSymbols {
    get {
      IEnumerable<INode> childStatements = Body?.Visit(node => node is Statement) ?? Enumerable.Empty<INode>();
      return Outs.Concat(childStatements.OfType<VarDeclStmt>().SelectMany(v => (IEnumerable<ISymbol>)v.Locals));
    }
  }

  public bool ShouldVerify => true; // This could be made more accurate
  public ModuleDefinition ContainingModule => EnclosingClass.EnclosingModuleDefinition;

  public void AutoRevealDependencies(AutoRevealFunctionDependencies Rewriter, DafnyOptions Options,
    ErrorReporter reporter) {
    if (Body is null) {
      return;
    }

    object? autoRevealDepsVal = null;
    bool autoRevealDeps = Attributes.ContainsMatchingValue(Attributes, "autoRevealDependencies",
      ref autoRevealDepsVal, new HashSet<Attributes.MatchingValueOption> {
        Attributes.MatchingValueOption.Bool,
        Attributes.MatchingValueOption.Int
      }, s => reporter.Error(MessageSource.Rewriter, ErrorLevel.Error, Origin, s));

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

    foreach (var func in Rewriter.GetEnumerator(this, currentClass, SubExpressions)) {
      var revealStmt =
        AutoRevealFunctionDependencies.BuildRevealStmt(func.Function, Origin, EnclosingClass.EnclosingModuleDefinition);

      if (revealStmt is not null) {
        addedReveals.Add(new AutoRevealFunctionDependencies.RevealStmtWithDepth(revealStmt, func.Depth));
      }
    }

    if (autoRevealDepth > 0) {
      Expression reqExpr = Expression.CreateBoolLiteral(Origin, true);

      foreach (var revealStmt in addedReveals) {
        if (revealStmt.Depth <= autoRevealDepth) {
          if (this is Constructor c) {
            c.BodyInit!.Insert(0, revealStmt.RevealStmt);
          } else {
            Body.Prepend(revealStmt.RevealStmt);
          }

          reqExpr = new StmtExpr(reqExpr.Origin, revealStmt.RevealStmt, reqExpr) {
            Type = Type.Bool
          };
        } else {
          break;
        }
      }

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

  public void ResolveNewOrOldPart(INewOrOldResolver resolver) {
    ResolveMethodOrFunction(resolver);
  }
}