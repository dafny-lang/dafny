using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class Method : MethodOrFunction, TypeParameter.ParentType, IMethodCodeContext, ICanFormat {
  public override IEnumerable<Node> Children => new Node[] { Body, Decreases }.
    Where(x => x != null).Concat(Ins).Concat(Outs).Concat<Node>(TypeArgs).
    Concat(Req).Concat(Ens).Concat(Mod.Expressions);
  public override IEnumerable<Node> PreResolveChildren => Children;

  public override string WhatKind => "method";
  public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
  public readonly IToken SignatureEllipsis;
  public readonly bool IsByMethod;
  public bool MustReverify;
  public bool IsEntryPoint = false;
  public readonly List<Formal> Ins;
  public readonly List<Formal> Outs;
  public readonly Specification<FrameExpression> Mod;
  private BlockStmt methodBody;  // Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution (note that "methodBody" is a "DividedBlockStmt" for any "Method" that is a "Constructor")
  [FilledInDuringResolution] public bool IsRecursive;
  [FilledInDuringResolution] public bool IsTailRecursive;
  public readonly ISet<IVariable> AssignedAssumptionVariables = new HashSet<IVariable>();
  public Method OverriddenMethod;
  public Method Original => OverriddenMethod == null ? this : OverriddenMethod.Original;
  public override bool IsOverrideThatAddsBody => base.IsOverrideThatAddsBody && Body != null;
  private static BlockStmt emptyBody = new BlockStmt(Token.NoToken.ToRange(), new List<Statement>());

  public bool HasPostcondition =>
    Ens.Count > 0 || Outs.Any(f => f.Type.AsSubsetType is not null);

  public bool HasPrecondition =>
    Req.Count > 0 || Ins.Any(f => f.Type.AsSubsetType is not null);

  public override IEnumerable<AssumptionDescription> Assumptions() {
    foreach (var a in base.Assumptions()) {
      yield return a;
    }

    if (Body is null && HasPostcondition && !EnclosingClass.EnclosingModuleDefinition.IsAbstract) {
      yield return AssumptionDescription.NoBody(IsGhost);
    }

    if (Attributes.Contains(Attributes, "extern") && HasPostcondition) {
      yield return AssumptionDescription.ExternWithPostcondition;
    }

    if (Attributes.Contains(Attributes, "extern") && HasPrecondition) {
      yield return AssumptionDescription.ExternWithPrecondition;
    }

    if (AllowsNontermination) {
      yield return AssumptionDescription.MayNotTerminate;
    }

    foreach (var c in Descendants()) {
      foreach (var a in c.Assumptions()) {
        yield return a;
      }
    }

  }

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var formal in Ins.Where(f => f.DefaultValue != null)) {
        yield return formal.DefaultValue;
      }
      foreach (var e in Req) {
        yield return e.E;
      }
      foreach (var e in Mod.Expressions) {
        yield return e.E;
      }
      foreach (var e in Ens) {
        yield return e.E;
      }
      foreach (var e in Decreases.Expressions) {
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
    Contract.Invariant(Mod != null);
    Contract.Invariant(cce.NonNullElements(Ens));
    Contract.Invariant(Decreases != null);
  }

  public Method(RangeToken rangeToken, Name name,
    bool hasStaticKeyword, bool isGhost,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IToken signatureEllipsis, bool isByMethod = false)
    : base(rangeToken, name, hasStaticKeyword, isGhost, attributes, signatureEllipsis != null,
      typeArgs, req, ens, decreases) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ins));
    Contract.Requires(cce.NonNullElements(outs));
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
    this.Ins = ins;
    this.Outs = outs;
    this.Mod = mod;
    this.methodBody = body;
    this.SignatureEllipsis = signatureEllipsis;
    this.IsByMethod = isByMethod;
    MustReverify = false;
  }

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
      return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
    }
  }

  public override string CompileName {
    get {
      var nm = base.CompileName;
      if (nm == Dafny.Compilers.SinglePassCompiler.DefaultNameMain && IsStatic && !IsEntryPoint) {
        // for a static method that is named "Main" but is not a legal "Main" method,
        // change its name.
        nm = EnclosingClass.Name + "_" + nm;
      }
      return nm;
    }
  }

  public BlockStmt Body {
    get {
      // Lemma from included files do not need to be resolved and translated
      // so we return emptyBody. This is to speed up resolver and translator.
      if (methodBody != null && IsLemmaLike && this.tok is IncludeToken && !DafnyOptions.O.VerifyAllModules) {
        return Method.emptyBody;
      } else {
        return methodBody;
      }
    }
    set {
      methodBody = value;
    }
  }

  public bool IsLemmaLike => this is Lemma || this is TwoStateLemma || this is ExtremeLemma || this is PrefixLemma;

  public BlockStmt BodyForRefinement {
    // For refinement, we still need to merge in the body
    // a lemma that is in the refinement base that is defined
    // in a include file.
    get {
      return methodBody;
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    if (BodyStartTok.line > 0) {
      formatter.SetDelimiterIndentedRegions(BodyStartTok, indentBefore);
    }

    formatter.SetFormalsIndentation(Ins);
    formatter.SetFormalsIndentation(Outs);
    foreach (var req in Req) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var mod in Mod.Expressions) {
      formatter.SetFrameExpressionIndentation(mod, indentBefore + formatter.SpaceTab);
    }

    foreach (var ens in Ens) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    foreach (var dec in Decreases.Expressions) {
      formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
      formatter.SetExpressionIndentation(dec);
    }

    if (Body != null) {
      formatter.SetStatementIndentation(this.Body);
    }

    return true;
  }

  protected override bool Bodyless => Body == null;
  protected override string TypeName => "method";

  /// <summary>
  /// Assumes type parameters have already been pushed
  /// </summary>
  public override void Resolve(Resolver resolver) {
    Contract.Requires(this != null);
    Contract.Requires(resolver.AllTypeConstraints.Count == 0);
    Contract.Ensures(resolver.AllTypeConstraints.Count == 0);

    base.Resolve(resolver);

    try {
      resolver.currentMethod = this;

      // make note of the warnShadowing attribute
      bool warnShadowingOption = DafnyOptions.O.WarnShadowing;  // save the original warnShadowing value
      bool warnShadowing = false;
      if (Attributes.ContainsBool(Attributes, "warnShadowing", ref warnShadowing)) {
        DafnyOptions.O.WarnShadowing = warnShadowing;  // set the value according to the attribute
      }

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      resolver.scope.PushMarker();
      if (IsStatic || this is Constructor) {
        resolver.scope.AllowInstance = false;
      }
      foreach (Formal p in Ins) {
        resolver.scope.Push(p.Name, p);
      }

      resolver.ResolveParameterDefaultValues(Ins, new ResolutionContext(this, this is TwoStateLemma));

      // Start resolving specification...
      foreach (AttributedExpression e in Req) {
        resolver.ResolveAttributes(e, new ResolutionContext(this, this is TwoStateLemma));
        resolver.ResolveExpression(e.E, new ResolutionContext(this, this is TwoStateLemma));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        resolver.ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      resolver.ResolveAttributes(Mod, new ResolutionContext(this, false));
      foreach (FrameExpression fe in Mod.Expressions) {
        resolver.ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Modifies, this);
        if (IsLemmaLike) {
          resolver.reporter.Error(MessageSource.Resolver, fe.tok, "{0}s are not allowed to have modifies clauses", WhatKind);
        } else if (IsGhost) {
          resolver.DisallowNonGhostFieldSpecifiers(fe);
        }
      }

      resolver.ResolveAttributes(Decreases, new ResolutionContext(this, false));
      foreach (Expression e in Decreases.Expressions) {
        resolver.ResolveExpression(e, new ResolutionContext(this, this is TwoStateLemma));
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
        resolver.reporter.Error(MessageSource.Resolver, Outs[0].tok, "{0}s are not allowed to have out-parameters", WhatKind);
      } else {
        foreach (Formal p in Outs) {
          resolver.scope.Push(p.Name, p);
        }
      }

      // ... continue resolving specification
      foreach (AttributedExpression e in Ens) {
        resolver.ResolveAttributes(e, new ResolutionContext(this, true));
        resolver.ResolveExpression(e.E, new ResolutionContext(this, true));
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
      resolver.ResolveAttributes(this, new ResolutionContext(this, this is TwoStateLemma), true);

      DafnyOptions.O.WarnShadowing = warnShadowingOption; // restore the original warnShadowing value
      resolver.scope.PopMarker();  // for the out-parameters and outermost-level locals
      resolver.scope.PopMarker();  // for the in-parameters

    }
    finally {
      resolver.currentMethod = null;
    }
  }
}