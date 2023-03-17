using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class MemberDecl : Declaration {
  public abstract string WhatKind { get; }
  public virtual string WhatKindMentionGhost => (IsGhost ? "ghost " : "") + WhatKind;
  public readonly bool HasStaticKeyword;
  public virtual bool IsStatic {
    get {
      return HasStaticKeyword || (EnclosingClass is ClassDecl && ((ClassDecl)EnclosingClass).IsDefaultClass);
    }
  }

  public virtual bool IsOpaque => false;

  protected readonly bool isGhost;
  public bool IsGhost { get { return isGhost; } }

  /// <summary>
  /// The term "instance independent" can be confusing. It means that the constant does not get its value in
  /// a constructor. (But the RHS of the const's declaration may mention "this".)
  /// </summary>
  public bool IsInstanceIndependentConstant => this is ConstantField cf && cf.Rhs != null;

  public TopLevelDecl EnclosingClass;  // filled in during resolution
  [FilledInDuringResolution] public MemberDecl RefinementBase;  // filled in during the pre-resolution refinement transformation; null if the member is new here
  [FilledInDuringResolution] public MemberDecl OverriddenMember;  // non-null if the member overrides a member in a parent trait
  public virtual bool IsOverrideThatAddsBody => OverriddenMember != null;

  /// <summary>
  /// Returns "true" if "this" is a (possibly transitive) override of "possiblyOverriddenMember".
  /// </summary>
  public bool Overrides(MemberDecl possiblyOverriddenMember) {
    Contract.Requires(possiblyOverriddenMember != null);
    for (var th = this; th != null; th = th.OverriddenMember) {
      if (th == possiblyOverriddenMember) {
        return true;
      }
    }
    return false;
  }

  public MemberDecl(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining)
    : base(rangeToken, name, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    HasStaticKeyword = hasStaticKeyword;
    this.isGhost = isGhost;
  }
  /// <summary>
  /// Returns className+"."+memberName.  Available only after resolution.
  /// </summary>
  public virtual string FullDafnyName {
    get {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string n = EnclosingClass.FullDafnyName;
      return (n.Length == 0 ? n : (n + ".")) + Name;
    }
  }
  public virtual string FullName {
    get {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return EnclosingClass.FullName + "." + Name;
    }
  }

  public override string SanitizedName =>
    (Name == EnclosingClass.Name ? "_" : "") + base.SanitizedName;

  public override string GetCompileName(DafnyOptions options) => (Name == EnclosingClass.Name ? "_" : "") + base.GetCompileName(options);

  public virtual string FullSanitizedName {
    get {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      if (Name == "requires") {
        return Translator.Requires(((ArrowTypeDecl)EnclosingClass).Arity);
      } else if (Name == "reads") {
        return Translator.Reads(((ArrowTypeDecl)EnclosingClass).Arity);
      } else {
        return EnclosingClass.FullSanitizedName + "." + SanitizedName;
      }
    }
  }

  public virtual IEnumerable<Expression> SubExpressions => Enumerable.Empty<Expression>();
}

public class Field : MemberDecl, ICanFormat, IHasDocstring {
  public override string WhatKind => "field";
  public readonly bool IsMutable;  // says whether or not the field can ever change values
  public readonly bool IsUserMutable;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)
  public readonly Type Type;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Type != null);
    Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
  }

  public override IEnumerable<Node> Children => Type.Nodes;

  public Field(RangeToken rangeToken, Name name, bool isGhost, Type type, Attributes attributes)
    : this(rangeToken, name, false, isGhost, true, true, type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
  }

  public Field(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : base(rangeToken, name, hasStaticKeyword, isGhost, attributes, false) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    Contract.Requires(!isUserMutable || isMutable);
    IsMutable = isMutable;
    IsUserMutable = isUserMutable;
    Type = type;
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetOpeningIndentedRegion(StartToken, indentBefore);
    formatter.SetIndentations(EndToken, below: indentBefore);
    var hasComma = OwnedTokens.Any(token => token.val == ",");
    switch (this) {
      case ConstantField constantField:
        var ownedTokens = constantField.OwnedTokens;
        var commaIndent = indentBefore + formatter.SpaceTab;
        var rightIndent = indentBefore + formatter.SpaceTab;
        foreach (var token in ownedTokens) {
          switch (token.val) {
            case ":=": {
                if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
                  formatter.SetDelimiterInsideIndentedRegions(token, indentBefore);
                } else if (formatter.ReduceBlockiness && token.Next.val is "{" or "[" or "(") {
                  if (!hasComma) {
                    rightIndent = indentBefore;
                    commaIndent = indentBefore;
                  } else {
                    rightIndent = indentBefore + formatter.SpaceTab;
                    commaIndent = indentBefore + formatter.SpaceTab;
                  }

                  formatter.SetIndentations(token, indentBefore, indentBefore, rightIndent);
                } else {
                  formatter.SetAlign(indentBefore + formatter.SpaceTab, token, out rightIndent, out commaIndent);
                }

                break;
              }
            case ",": {
                formatter.SetIndentations(token, rightIndent, commaIndent, rightIndent);
                break;
              }
            case ";": {
                break;
              }
          }
        }

        if (constantField.Rhs is { } constantFieldRhs) {
          formatter.SetExpressionIndentation(constantFieldRhs);
        }

        break;
    }

    return true;
  }

  protected override string GetTriviaContainingDocstring() {
    if (EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokeOrNull();
  }
}

public class SpecialFunction : Function, ICallable {
  readonly ModuleDefinition Module;
  public SpecialFunction(RangeToken rangeToken, string name, ModuleDefinition module, bool hasStaticKeyword, bool isGhost,
    List<TypeParameter> typeArgs, List<Formal> formals, Type resultType,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, new Name(name), hasStaticKeyword, isGhost, false, typeArgs, formals, null, resultType, req, reads, ens, decreases, body, null, null, attributes, signatureEllipsis) {
    Module = module;
  }
  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return this.Module; } }
  string ICallable.NameRelativeToModule { get { return Name; } }
}

public class SpecialField : Field {
  public enum ID {
    UseIdParam,  // IdParam is a string
    ArrayLength,  // IdParam is null for .Length; IdParam is an int "x" for GetLength(x)
    ArrayLengthInt,  // same as ArrayLength, but produces int instead of BigInteger
    Floor,
    IsLimit,
    IsSucc,
    Offset,
    IsNat,
    Keys,
    Values,
    Items,
    Reads,
    Modifies,
    New,
  }
  public readonly ID SpecialId;
  public readonly object IdParam;

  public SpecialField(RangeToken rangeToken, string name, ID specialId, object idParam,
    bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : this(rangeToken, new Name(name), specialId, idParam, false, isGhost, isMutable, isUserMutable, type, attributes) {
  }

  public SpecialField(RangeToken rangeToken, Name name, ID specialId, object idParam,
    bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : base(rangeToken, name, hasStaticKeyword, isGhost, isMutable, isUserMutable, type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(!isUserMutable || isMutable);
    Contract.Requires(type != null);

    SpecialId = specialId;
    IdParam = idParam;
  }

  public override string FullName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullName + "." + Name : Name;
    }
  }

  public override string FullSanitizedName { // Override beacuse EnclosingClass may be null
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullSanitizedName + "." + SanitizedName : SanitizedName;
    }
  }

  public override string GetCompileName(DafnyOptions options) {
    Contract.Ensures(Contract.Result<string>() != null);
    return EnclosingClass != null ? base.GetCompileName(options) : Name;
  }
}

public class DatatypeDiscriminator : SpecialField {
  public override string WhatKind {
    get { return "discriminator"; }
  }

  public DatatypeDiscriminator(RangeToken rangeToken, Name name, ID specialId, object idParam, bool isGhost, Type type, Attributes attributes)
    : base(rangeToken, name, specialId, idParam, false, isGhost, false, false, type, attributes) {
  }
}

public class DatatypeDestructor : SpecialField {
  public readonly List<DatatypeCtor> EnclosingCtors = new List<DatatypeCtor>();  // is always a nonempty list
  public readonly List<Formal> CorrespondingFormals = new List<Formal>();  // is always a nonempty list
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(EnclosingCtors != null);
    Contract.Invariant(CorrespondingFormals != null);
    Contract.Invariant(EnclosingCtors.Count > 0);
    Contract.Invariant(EnclosingCtors.Count == CorrespondingFormals.Count);
  }

  public DatatypeDestructor(RangeToken rangeToken, DatatypeCtor enclosingCtor, Formal correspondingFormal, Name name, string compiledName, bool isGhost, Type type, Attributes attributes)
    : base(rangeToken, name, SpecialField.ID.UseIdParam, compiledName, false, isGhost, false, false, type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(enclosingCtor != null);
    Contract.Requires(correspondingFormal != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    EnclosingCtors.Add(enclosingCtor);  // more enclosing constructors may be added later during resolution
    CorrespondingFormals.Add(correspondingFormal);  // more corresponding formals may be added later during resolution
  }

  /// <summary>
  /// To be called only by the resolver. Called to share this datatype destructor between multiple constructors
  /// of the same datatype.
  /// </summary>
  internal void AddAnotherEnclosingCtor(DatatypeCtor ctor, Formal formal) {
    Contract.Requires(ctor != null);
    Contract.Requires(formal != null);
    EnclosingCtors.Add(ctor);  // more enclosing constructors may be added later during resolution
    CorrespondingFormals.Add(formal);  // more corresponding formals may be added later during resolution
  }

  internal string EnclosingCtorNames(string grammaticalConjunction) {
    Contract.Requires(grammaticalConjunction != null);
    return PrintableCtorNameList(EnclosingCtors, grammaticalConjunction);
  }

  static internal string PrintableCtorNameList(List<DatatypeCtor> ctors, string grammaticalConjunction) {
    Contract.Requires(ctors != null);
    Contract.Requires(grammaticalConjunction != null);
    return Util.PrintableNameList(ctors.ConvertAll(ctor => ctor.Name), grammaticalConjunction);
  }
}

public class ConstantField : SpecialField, ICallable {
  public override string WhatKind => "const field";
  public readonly Expression Rhs;

  public override bool IsOpaque { get; }

  public ConstantField(RangeToken rangeToken, Name name, Expression/*?*/ rhs, bool hasStaticKeyword, bool isGhost, bool isOpaque, Type type, Attributes attributes)
      : base(rangeToken, name, ID.UseIdParam, NonglobalVariable.SanitizeName(name.Value), hasStaticKeyword, isGhost, false, false, type, attributes) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    this.Rhs = rhs;
    this.IsOpaque = isOpaque;
  }

  public override bool CanBeRevealed() {
    return true;
  }

  //
  public new bool IsGhost { get { return this.isGhost; } }
  public List<TypeParameter> TypeArgs { get { return new List<TypeParameter>(); } }
  public List<Formal> Ins { get { return new List<Formal>(); } }
  public ModuleDefinition EnclosingModule { get { return this.EnclosingClass.EnclosingModuleDefinition; } }
  public bool MustReverify { get { return false; } }
  public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
  public string NameRelativeToModule {
    get {
      if (EnclosingClass is DefaultClassDecl) {
        return Name;
      } else {
        return EnclosingClass.Name + "." + Name;
      }
    }
  }
  public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
  public bool InferredDecreases {
    get { throw new cce.UnreachableException(); }
    set { throw new cce.UnreachableException(); }
  }
  public bool AllowsAllocation => true;

  public override IEnumerable<Node> Children => base.Children.Concat(new[] { Rhs }.Where(x => x != null));

  public override IEnumerable<Node> PreResolveChildren => Children;
}

public class Predicate : Function {
  public override string WhatKind => "predicate";
  public enum BodyOriginKind {
    OriginalOrInherited,  // this predicate definition is new (and the predicate may or may not have a body), or the predicate's body (whether or not it exists) is being inherited unmodified (from the previous refinement--it may be that the inherited body was itself an extension, for example)
    DelayedDefinition,  // this predicate declaration provides, for the first time, a body--the declaration refines a previously declared predicate, but the previous one had no body
    Extension  // this predicate extends the definition of a predicate with a body in a module being refined
  }
  public readonly BodyOriginKind BodyOrigin;
  public Predicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> formals,
    Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, BodyOriginKind bodyOrigin, IToken/*?*/ byMethodTok, BlockStmt/*?*/ byMethodBody, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, isGhost, isOpaque, typeArgs, formals, result, Type.Bool, req, reads, ens, decreases, body, byMethodTok, byMethodBody, attributes, signatureEllipsis) {
    Contract.Requires(bodyOrigin == Predicate.BodyOriginKind.OriginalOrInherited || body != null);
    BodyOrigin = bodyOrigin;
  }
}

/// <summary>
/// An PrefixPredicate is the inductive unrolling P# implicitly declared for every extreme predicate P.
/// </summary>
public class PrefixPredicate : Function {
  public override string WhatKind => "prefix predicate";
  public override string WhatKindMentionGhost => WhatKind;
  public readonly Formal K;
  public readonly ExtremePredicate ExtremePred;
  public PrefixPredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword,
    List<TypeParameter> typeArgs, Formal k, List<Formal> formals,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, ExtremePredicate extremePred)
    : base(rangeToken, name, hasStaticKeyword, true, false, typeArgs, formals, null, Type.Bool, req, reads, ens, decreases, body, null, null, attributes, null) {
    Contract.Requires(k != null);
    Contract.Requires(extremePred != null);
    Contract.Requires(formals != null && 1 <= formals.Count && formals[0] == k);
    K = k;
    ExtremePred = extremePred;
  }
}

public abstract class ExtremePredicate : Function {
  public override string WhatKindMentionGhost => WhatKind;
  public enum KType { Unspecified, Nat, ORDINAL }
  public readonly KType TypeOfK;
  public bool KNat {
    get {
      return TypeOfK == KType.Nat;
    }
  }
  [FilledInDuringResolution] public readonly List<FunctionCallExpr> Uses = new List<FunctionCallExpr>();  // used by verifier
  [FilledInDuringResolution] public PrefixPredicate PrefixPredicate;  // (name registration)

  public override IEnumerable<Node> Children => base.Children.Concat(new[] { PrefixPredicate });
  public override IEnumerable<Node> PreResolveChildren => base.Children;

  public ExtremePredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, isOpaque, typeArgs, formals, result, Type.Bool,
      req, reads, ens, new Specification<Expression>(new List<Expression>(), null), body, null, null, attributes, signatureEllipsis) {
    TypeOfK = typeOfK;
  }

  /// <summary>
  /// For the given call P(s), return P#[depth](s).  The resulting expression shares some of the subexpressions
  /// with 'fexp' (that is, what is returned is not necessarily a clone).
  /// </summary>
  public FunctionCallExpr CreatePrefixPredicateCall(FunctionCallExpr fexp, Expression depth) {
    Contract.Requires(fexp != null);
    Contract.Requires(fexp.Function == this);
    Contract.Requires(depth != null);
    Contract.Ensures(Contract.Result<FunctionCallExpr>() != null);

    var args = new List<Expression>() { depth };
    args.AddRange(fexp.Args);
    var prefixPredCall = new FunctionCallExpr(fexp.Tok, this.PrefixPredicate.Name, fexp.Receiver, fexp.OpenParen, fexp.CloseParen, args);
    prefixPredCall.Function = this.PrefixPredicate;  // resolve here
    prefixPredCall.TypeApplication_AtEnclosingClass = fexp.TypeApplication_AtEnclosingClass;  // resolve here
    prefixPredCall.TypeApplication_JustFunction = fexp.TypeApplication_JustFunction;  // resolve here
    prefixPredCall.Type = fexp.Type;  // resolve here
    prefixPredCall.CoCall = fexp.CoCall;  // resolve here
    return prefixPredCall;
  }
}

public class LeastPredicate : ExtremePredicate {
  public override string WhatKind => "least predicate";
  public LeastPredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, isOpaque, typeOfK, typeArgs, formals, result,
      req, reads, ens, body, attributes, signatureEllipsis) {
  }
}

public class GreatestPredicate : ExtremePredicate {
  public override string WhatKind => "greatest predicate";
  public GreatestPredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque, KType typeOfK,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, isOpaque, typeOfK, typeArgs, formals, result,
      req, reads, ens, body, attributes, signatureEllipsis) {
  }
}

public class TwoStateFunction : Function {
  public override string WhatKind => "twostate function";
  public override string WhatKindMentionGhost => WhatKind;
  public TwoStateFunction(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result, Type resultType,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, isOpaque, typeArgs, formals, result, resultType, req, reads, ens, decreases, body, null, null, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(formals != null);
    Contract.Requires(resultType != null);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(ens != null);
    Contract.Requires(decreases != null);
  }
  public override bool ReadsHeap { get { return true; } }
}

public class TwoStatePredicate : TwoStateFunction {
  public override string WhatKind => "twostate predicate";
  public TwoStatePredicate(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isOpaque,
    List<TypeParameter> typeArgs, List<Formal> formals, Formal result,
    List<AttributedExpression> req, List<FrameExpression> reads, List<AttributedExpression> ens, Specification<Expression> decreases,
    Expression body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, isOpaque, typeArgs, formals, result, Type.Bool, req, reads, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(formals != null);
    Contract.Requires(req != null);
    Contract.Requires(reads != null);
    Contract.Requires(ens != null);
    Contract.Requires(decreases != null);
  }
}

public class Lemma : Method {
  public override string WhatKind => "lemma";
  public override string WhatKindMentionGhost => WhatKind;
  public Lemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
  }

  public override bool AllowsAllocation => false;
}

public class TwoStateLemma : Method {
  public override string WhatKind => "twostate lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public TwoStateLemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword,
    [Captured] List<TypeParameter> typeArgs,
    [Captured] List<Formal> ins, [Captured] List<Formal> outs,
    [Captured] List<AttributedExpression> req,
    [Captured] Specification<FrameExpression> mod,
    [Captured] List<AttributedExpression> ens,
    [Captured] Specification<Expression> decreases,
    [Captured] BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(ins != null);
    Contract.Requires(outs != null);
    Contract.Requires(req != null);
    Contract.Requires(mod != null);
    Contract.Requires(ens != null);
    Contract.Requires(decreases != null);
  }

  public override bool AllowsAllocation => false;
}

public class Constructor : Method {
  public override string WhatKind => "constructor";
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Body == null || Body is DividedBlockStmt);
  }
  public List<Statement> BodyInit {  // first part of Body's statements
    get {
      if (Body == null) {
        return null;
      } else {
        return ((DividedBlockStmt)Body).BodyInit;
      }
    }
  }
  public List<Statement> BodyProper {  // second part of Body's statements
    get {
      if (Body == null) {
        return null;
      } else {
        return ((DividedBlockStmt)Body).BodyProper;
      }
    }
  }
  public Constructor(RangeToken rangeToken, Name name,
    bool isGhost,
    List<TypeParameter> typeArgs,
    List<Formal> ins,
    List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    DividedBlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, false, isGhost, typeArgs, ins, new List<Formal>(), req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ins));
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
  }

  public bool HasName {
    get {
      return Name != "_ctor";
    }
  }
}

/// <summary>
/// A PrefixLemma is the inductive unrolling M# implicitly declared for every extreme lemma M.
/// </summary>
public class PrefixLemma : Method {
  public override string WhatKind => "prefix lemma";
  public override string WhatKindMentionGhost => WhatKind;

  public readonly Formal K;
  public readonly ExtremeLemma ExtremeLemma;
  public PrefixLemma(RangeToken rangeToken, Name name, bool hasStaticKeyword,
    List<TypeParameter> typeArgs, Formal k, List<Formal> ins, List<Formal> outs,
    List<AttributedExpression> req, Specification<FrameExpression> mod, List<AttributedExpression> ens, Specification<Expression> decreases,
    BlockStmt body, Attributes attributes, ExtremeLemma extremeLemma)
    : base(rangeToken, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, null) {
    Contract.Requires(k != null);
    Contract.Requires(ins != null && 1 <= ins.Count && ins[0] == k);
    Contract.Requires(extremeLemma != null);
    K = k;
    ExtremeLemma = extremeLemma;
  }

  public override bool AllowsAllocation => false;
}

public abstract class ExtremeLemma : Method {
  public override string WhatKindMentionGhost => WhatKind;
  public readonly ExtremePredicate.KType TypeOfK;
  public bool KNat {
    get {
      return TypeOfK == ExtremePredicate.KType.Nat;
    }
  }
  [FilledInDuringResolution] public PrefixLemma PrefixLemma;  // (name registration)

  public override IEnumerable<Node> Children => base.Children.Concat(new[] { PrefixLemma });

  public override IEnumerable<Node> PreResolveChildren => base.Children;

  public ExtremeLemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
    List<TypeParameter> typeArgs,
    List<Formal> ins, [Captured] List<Formal> outs,
    List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, true, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ins));
    Contract.Requires(cce.NonNullElements(outs));
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
    TypeOfK = typeOfK;
  }

  public override bool AllowsAllocation => false;
}

public class LeastLemma : ExtremeLemma {
  public override string WhatKind => "least lemma";

  public LeastLemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
    List<TypeParameter> typeArgs,
    List<Formal> ins, [Captured] List<Formal> outs,
    List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, typeOfK, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ins));
    Contract.Requires(cce.NonNullElements(outs));
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
  }
}

public class GreatestLemma : ExtremeLemma {
  public override string WhatKind => "greatest lemma";

  public GreatestLemma(RangeToken rangeToken, Name name,
    bool hasStaticKeyword, ExtremePredicate.KType typeOfK,
    List<TypeParameter> typeArgs,
    List<Formal> ins, [Captured] List<Formal> outs,
    List<AttributedExpression> req, [Captured] Specification<FrameExpression> mod,
    List<AttributedExpression> ens,
    Specification<Expression> decreases,
    BlockStmt body,
    Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, hasStaticKeyword, typeOfK, typeArgs, ins, outs, req, mod, ens, decreases, body, attributes, signatureEllipsis) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ins));
    Contract.Requires(cce.NonNullElements(outs));
    Contract.Requires(cce.NonNullElements(req));
    Contract.Requires(mod != null);
    Contract.Requires(cce.NonNullElements(ens));
    Contract.Requires(decreases != null);
  }
}