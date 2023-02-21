using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class IteratorDecl : ClassDecl, IMethodCodeContext {
  public override string WhatKind { get { return "iterator"; } }
  public readonly List<Formal> Ins;
  public readonly List<Formal> Outs;
  public readonly Specification<FrameExpression> Reads;
  public readonly Specification<FrameExpression> Modifies;
  public readonly Specification<Expression> Decreases;
  public readonly List<AttributedExpression> Requires;
  public readonly List<AttributedExpression> Ensures;
  public readonly List<AttributedExpression> YieldRequires;
  public readonly List<AttributedExpression> YieldEnsures;
  public readonly BlockStmt Body;
  public bool SignatureIsOmitted { get { return SignatureEllipsis != null; } }
  public readonly IToken SignatureEllipsis;
  public readonly List<Field> OutsFields;
  public readonly List<Field> OutsHistoryFields;  // these are the 'xs' variables
  [FilledInDuringResolution] public readonly List<Field> DecreasesFields;
  [FilledInDuringResolution] public SpecialField Member_Modifies;
  [FilledInDuringResolution] public SpecialField Member_Reads;
  [FilledInDuringResolution] public SpecialField Member_New;
  [FilledInDuringResolution] public Constructor Member_Init;  // created during registration phase of resolution;
  [FilledInDuringResolution] public Predicate Member_Valid;  // created during registration phase of resolution;
  [FilledInDuringResolution] public Method Member_MoveNext;  // created during registration phase of resolution;
  public readonly LocalVariable YieldCountVariable;

  public IteratorDecl(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    List<Formal> ins, List<Formal> outs,
    Specification<FrameExpression> reads, Specification<FrameExpression> mod, Specification<Expression> decreases,
    List<AttributedExpression> requires,
    List<AttributedExpression> ensures,
    List<AttributedExpression> yieldRequires,
    List<AttributedExpression> yieldEnsures,
    BlockStmt body, Attributes attributes, IToken signatureEllipsis)
    : base(rangeToken, name, module, typeArgs, new List<MemberDecl>(), attributes, signatureEllipsis != null, null) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(ins != null);
    Contract.Requires(outs != null);
    Contract.Requires(reads != null);
    Contract.Requires(mod != null);
    Contract.Requires(decreases != null);
    Contract.Requires(requires != null);
    Contract.Requires(ensures != null);
    Contract.Requires(yieldRequires != null);
    Contract.Requires(yieldEnsures != null);
    Ins = ins;
    Outs = outs;
    Reads = reads;
    Modifies = mod;
    Decreases = decreases;
    Requires = requires;
    Ensures = ensures;
    YieldRequires = yieldRequires;
    YieldEnsures = yieldEnsures;
    Body = body;
    SignatureEllipsis = signatureEllipsis;

    OutsFields = new List<Field>();
    OutsHistoryFields = new List<Field>();
    DecreasesFields = new List<Field>();

    YieldCountVariable = new LocalVariable(rangeToken, "_yieldCount", new EverIncreasingType(), true);
    YieldCountVariable.type = YieldCountVariable.OptionalType;  // resolve YieldCountVariable here
  }

  /// <summary>
  /// Returns the non-null expressions of this declaration proper (that is, do not include the expressions of substatements).
  /// Does not include the generated class members.
  /// </summary>
  public virtual IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      foreach (var e in Attributes.SubExpressions(Reads.Attributes)) {
        yield return e;
      }
      foreach (var e in Reads.Expressions) {
        yield return e.E;
      }
      foreach (var e in Attributes.SubExpressions(Modifies.Attributes)) {
        yield return e;
      }
      foreach (var e in Modifies.Expressions) {
        yield return e.E;
      }
      foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) {
        yield return e;
      }
      foreach (var e in Decreases.Expressions) {
        yield return e;
      }
      foreach (var e in Requires) {
        yield return e.E;
      }
      foreach (var e in Ensures) {
        yield return e.E;
      }
      foreach (var e in YieldRequires) {
        yield return e.E;
      }
      foreach (var e in YieldEnsures) {
        yield return e.E;
      }
    }
  }

  /// <summary>
  /// This Dafny type exists only for the purpose of giving the yield-count variable a type, so
  /// that the type can be recognized during translation of Dafny into Boogie.  It represents
  /// an integer component in a "decreases" clause whose order is (\lambda x,y :: x GREATER y),
  /// not the usual (\lambda x,y :: x LESS y AND 0 ATMOST y).
  /// </summary>
  public class EverIncreasingType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);

      return "_increasingInt";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is EverIncreasingType;
    }
  }

  bool ICodeContext.IsGhost { get { return false; } }
  List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
  List<Formal> ICodeContext.Ins { get { return this.Ins; } }
  List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
  Specification<FrameExpression> IMethodCodeContext.Modifies { get { return this.Modifies; } }
  string ICallable.NameRelativeToModule { get { return this.Name; } }
  Specification<Expression> ICallable.Decreases { get { return this.Decreases; } }
  bool _inferredDecr;
  bool ICallable.InferredDecreases {
    set { _inferredDecr = value; }
    get { return _inferredDecr; }
  }

  ModuleDefinition IASTVisitorContext.EnclosingModule { get { return this.EnclosingModuleDefinition; } }
  bool ICodeContext.MustReverify { get { return false; } }
  public bool AllowsNontermination {
    get {
      return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
    }
  }

  public override bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetMethodLikeIndent(StartToken, OwnedTokens, indentBefore);
    foreach (var req in Requires) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var req in Ensures) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var req in YieldRequires) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    foreach (var req in YieldEnsures) {
      formatter.SetAttributedExpressionIndentation(req, indentBefore + formatter.SpaceTab);
    }

    formatter.SetFormalsIndentation(Ins);
    formatter.SetFormalsIndentation(Outs);
    if (this.BodyStartTok.line > 0) {
      formatter.SetDelimiterIndentedRegions(this.BodyStartTok, indentBefore);
      formatter.SetClosingIndentedRegion(Token.NoToken, indentBefore);
    }

    if (Body != null) {
      formatter.SetStatementIndentation(Body);
    }

    return true;
  }
}