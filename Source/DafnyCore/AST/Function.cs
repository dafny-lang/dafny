using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class Function : MemberDecl, TypeParameter.ParentType, ICallable, ICanFormat {
  public override string WhatKind => "function";

  public string FunctionDeclarationKeywords {
    get {
      string k;
      if (this is TwoStateFunction || this is ExtremePredicate || this.ByMethodBody != null) {
        k = WhatKind;
      } else if (this is PrefixPredicate) {
        k = "predicate";
      } else if (DafnyOptions.O.FunctionSyntax == FunctionSyntaxOptions.ExperimentalPredicateAlwaysGhost &&
                 (this is Predicate || !IsGhost)) {
        k = WhatKind;
      } else if (DafnyOptions.O.FunctionSyntax != FunctionSyntaxOptions.Version4 && !IsGhost) {
        k = WhatKind + " method";
      } else if (DafnyOptions.O.FunctionSyntax != FunctionSyntaxOptions.Version3 && IsGhost) {
        k = "ghost " + WhatKind;
      } else {
        k = WhatKind;
      }

      return HasStaticKeyword ? "static " + k : k;
    }
  }

  public override bool CanBeRevealed() {
    return true;
  }

  public bool HasPostcondition =>
    Ens.Count > 0 || ResultType.AsSubsetType is not null;

  public bool HasPrecondition =>
    Req.Count > 0 || Formals.Any(f => f.Type.AsSubsetType is not null);

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

    foreach (var c in Descendants()) {
      foreach (var a in c.Assumptions()) {
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
  public bool IsAccumulatorTailRecursive => IsTailRecursive && TailRecursion != Function.TailStatus.TailRecursive;
  [FilledInDuringResolution] public bool IsFueled; // if anyone tries to adjust this function's fuel
  public readonly List<TypeParameter> TypeArgs;
  public readonly List<Formal> Formals;
  public readonly Formal Result;
  public readonly Type ResultType;
  public readonly List<AttributedExpression> Req;
  public readonly List<FrameExpression> Reads;
  public readonly List<AttributedExpression> Ens;
  public readonly Specification<Expression> Decreases;
  public Expression Body; // an extended expression; Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution
  public IToken /*?*/ ByMethodTok; // null iff ByMethodBody is null
  public BlockStmt /*?*/ ByMethodBody;
  [FilledInDuringResolution] public Method /*?*/ ByMethodDecl; // if ByMethodBody is non-null
  public bool SignatureIsOmitted => SignatureEllipsis != null; // is "false" for all Function objects that survive into resolution
  public readonly IToken SignatureEllipsis;
  public Function OverriddenFunction;
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

  public override IEnumerable<Node> Children => new[] { ByMethodDecl }.Where(x => x != null).
    Concat<Node>(TypeArgs).
    Concat<Node>(Reads).
    Concat<Node>(Req).
    Concat(Ens.Select(e => e.E)).
    Concat(Decreases.Expressions).
    Concat(Formals).Concat(ResultType != null ? new List<Node>() { ResultType } : new List<Node>()).
    Concat(Body == null ? Enumerable.Empty<Node>() : new[] { Body });

  public override IEnumerable<Node> PreResolveChildren => Children;

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var formal in Formals.Where(f => f.DefaultValue != null)) {
        yield return formal.DefaultValue;
      }
      foreach (var e in Req) {
        yield return e.E;
      }
      foreach (var e in Reads) {
        yield return e.E;
      }
      foreach (var e in Ens) {
        yield return e.E;
      }
      foreach (var e in Decreases.Expressions) {
        yield return e;
      }
      if (Body != null) {
        yield return Body;
      }
    }
  }

  public Type GetMemberType(ArrowTypeDecl atd) {
    Contract.Requires(atd != null);
    Contract.Requires(atd.Arity == Formals.Count);

    // Note, the following returned type can contain type parameters from the function and its enclosing class
    return new ArrowType(tok, atd, Formals.ConvertAll(f => f.Type), ResultType);
  }

  public bool AllowsNontermination {
    get {
      return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
    }
  }

  /// <summary>
  /// The "AllCalls" field is used for non-ExtremePredicate, non-PrefixPredicate functions only (so its value should not be relied upon for ExtremePredicate and PrefixPredicate functions).
  /// It records all function calls made by the Function, including calls made in the body as well as in the specification.
  /// The field is filled in during resolution (and used toward the end of resolution, to attach a helpful "decreases" prefix to functions in clusters
  /// with co-recursive calls.
  /// </summary>
  public readonly List<FunctionCallExpr> AllCalls = new List<FunctionCallExpr>();
  public enum CoCallClusterInvolvement {
    None,  // the SCC containing the function does not involve any co-recursive calls
    IsMutuallyRecursiveTarget,  // the SCC contains co-recursive calls, and this function is the target of some non-self recursive call
    CoRecursiveTargetAllTheWay,  // the SCC contains co-recursive calls, and this function is the target only of self-recursive calls and co-recursive calls
  }
  public CoCallClusterInvolvement CoClusterTarget = CoCallClusterInvolvement.None;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TypeArgs));
    Contract.Invariant(cce.NonNullElements(Formals));
    Contract.Invariant(ResultType != null);
    Contract.Invariant(cce.NonNullElements(Req));
    Contract.Invariant(cce.NonNullElements(Reads));
    Contract.Invariant(cce.NonNullElements(Ens));
    Contract.Invariant(Decreases != null);
  }

  public Function(RangeToken range, Name name, bool hasStaticKeyword, bool isGhost,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result, Type resultType,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression/*?*/ body, IToken/*?*/ byMethodTok, BlockStmt/*?*/ byMethodBody,
    Attributes attributes, IToken/*?*/ signatureEllipsis)
    : base(range, name, hasStaticKeyword, isGhost, attributes, signatureEllipsis != null) {

    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(formals));
    Contract.Requires(resultType != null);
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(cce.NonNullElements(reads));
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
    Contract.Requires(byMethodBody == null || (!isGhost && body != null)); // function-by-method has a ghost expr and non-ghost stmt, but to callers appears like a functiion-method
    this.IsFueled = false;  // Defaults to false.  Only set to true if someone mentions this function in a fuel annotation
    this.TypeArgs = typeArgs;
    this.Formals = formals;
    this.Result = result;
    this.ResultType = result != null ? result.Type : resultType;
    this.Req = req;
    this.Reads = reads;
    this.Ens = ens;
    this.Decreases = decreases;
    this.Body = body;
    this.ByMethodTok = byMethodTok;
    this.ByMethodBody = byMethodBody;
    this.SignatureEllipsis = signatureEllipsis;

    if (attributes != null) {
      List<Expression> args = Attributes.FindExpressions(attributes, "fuel");
      if (args != null) {
        if (args.Count == 1) {
          LiteralExpr literal = args[0] as LiteralExpr;
          if (literal != null && literal.Value is BigInteger) {
            this.IsFueled = true;
          }
        } else if (args.Count == 2) {
          LiteralExpr literalLow = args[0] as LiteralExpr;
          LiteralExpr literalHigh = args[1] as LiteralExpr;

          if (literalLow != null && literalLow.Value is BigInteger && literalHigh != null && literalHigh.Value is BigInteger) {
            this.IsFueled = true;
          }
        }
      }
    }
  }

  bool ICodeContext.IsGhost { get { return this.IsGhost; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return this.Formals; } }
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
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return this.EnclosingClass.EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }

  [Pure]
  public bool IsFuelAware() { return IsRecursive || IsFueled || (OverriddenFunction != null && OverriddenFunction.IsFuelAware()); }
  public virtual bool ReadsHeap { get { return Reads.Count != 0; } }

  public static readonly Option<string> FunctionSyntaxOption = new("--function-syntax",
    () => "3",
    @"
The syntax for functions is changing from Dafny version 3 to version 4. This switch gives early access to the new syntax, and also provides a mode to help with migration.

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
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    if (StartToken.line > 0) {
      formatter.SetDelimiterIndentedRegions(StartToken, indentBefore);
    }

    formatter.SetFormalsIndentation(Formals);
    if (Result is { } outFormal) {
      formatter.SetTypeIndentation(outFormal.SyntacticType);
    }

    foreach (var req in Req) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var frame in Reads) {
      formatter.SetFrameExpressionIndentation(frame, indentBefore + formatter.SpaceTab);
    }

    foreach (var ens in Ens) {
      formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
    }

    foreach (var dec in Decreases.Expressions) {
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
}
