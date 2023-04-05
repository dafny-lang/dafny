using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class IteratorDecl : ClassDecl, IMethodCodeContext, IHasDocstring {
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
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
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

  /// <summary>
  /// Assumes the specification of the iterator itself has been successfully resolved.
  /// </summary>
  public void CreateIteratorMethodSpecs(Resolver resolver) {
    Contract.Requires(this != null);

    var tok = new AutoGeneratedToken(Tok);

    // ---------- here comes the constructor ----------
    // same requires clause as the iterator itself
    Member_Init.Req.AddRange(Requires);
    var ens = Member_Init.Ens;
    foreach (var p in Ins) {
      // ensures this.x == x;
      ens.Add(new AttributedExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new IdentifierExpr(p.tok, p.Name))));
    }
    foreach (var p in OutsHistoryFields) {
      // ensures this.ys == [];
      ens.Add(new AttributedExpression(new BinaryExpr(p.tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(p.tok, new ThisExpr(p.tok), p.Name), new SeqDisplayExpr(p.tok, new List<Expression>()))));
    }
    // ensures this.Valid();
    var valid_call = new FunctionCallExpr(tok, "Valid", new ThisExpr(tok), tok, tok, new List<ActualBinding>());
    ens.Add(new AttributedExpression(valid_call));
    // ensures this._reads == old(ReadsClause);
    var modSetSingletons = new List<Expression>();
    Expression frameSet = new SetDisplayExpr(tok, true, modSetSingletons);
    foreach (var fr in Reads.Expressions) {
      if (fr.FieldName != null) {
        resolver.reporter.Error(MessageSource.Resolver, fr.tok, "sorry, a reads clause for an iterator is not allowed to designate specific fields");
      } else if (fr.E.Type.IsRefType) {
        modSetSingletons.Add(fr.E);
      } else {
        frameSet = new BinaryExpr(fr.tok, BinaryExpr.Opcode.Add, frameSet, fr.E);
      }
    }
    ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq,
      new MemberSelectExpr(tok, new ThisExpr(tok), "_reads"),
      new OldExpr(tok, frameSet))));
    // ensures this._modifies == old(ModifiesClause);
    modSetSingletons = new List<Expression>();
    frameSet = new SetDisplayExpr(tok, true, modSetSingletons);
    foreach (var fr in Modifies.Expressions) {
      if (fr.FieldName != null) {
        resolver.reporter.Error(MessageSource.Resolver, fr.tok, "sorry, a modifies clause for an iterator is not allowed to designate specific fields");
      } else if (fr.E.Type.IsRefType) {
        modSetSingletons.Add(fr.E);
      } else {
        frameSet = new BinaryExpr(fr.tok, BinaryExpr.Opcode.Add, frameSet, fr.E);
      }
    }
    ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq,
      new MemberSelectExpr(tok, new ThisExpr(tok), "_modifies"),
      new OldExpr(tok, frameSet))));
    // ensures this._new == {};
    ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq,
      new MemberSelectExpr(tok, new ThisExpr(tok), "_new"),
      new SetDisplayExpr(tok, true, new List<Expression>()))));
    // ensures this._decreases0 == old(DecreasesClause[0]) && ...;
    Contract.Assert(Decreases.Expressions.Count == DecreasesFields.Count);
    for (int i = 0; i < Decreases.Expressions.Count; i++) {
      var p = Decreases.Expressions[i];
      ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Eq,
        new MemberSelectExpr(tok, new ThisExpr(tok), DecreasesFields[i].Name),
        new OldExpr(tok, p))));
    }

    // ---------- here comes predicate Valid() ----------
    var reads = Member_Valid.Reads;
    reads.Add(new FrameExpression(tok, new ThisExpr(tok), null));  // reads this;
    reads.Add(new FrameExpression(tok, new MemberSelectExpr(tok, new ThisExpr(tok), "_reads"), null));  // reads this._reads;
    reads.Add(new FrameExpression(tok, new MemberSelectExpr(tok, new ThisExpr(tok), "_new"), null));  // reads this._new;

    // ---------- here comes method MoveNext() ----------
    // requires this.Valid();
    var req = Member_MoveNext.Req;
    valid_call = new FunctionCallExpr(tok, "Valid", new ThisExpr(tok), tok, tok, new List<ActualBinding>());
    req.Add(new AttributedExpression(valid_call));
    // requires YieldRequires;
    req.AddRange(YieldRequires);
    // modifies this, this._modifies, this._new;
    var mod = Member_MoveNext.Mod.Expressions;
    mod.Add(new FrameExpression(tok, new ThisExpr(tok), null));
    mod.Add(new FrameExpression(tok, new MemberSelectExpr(tok, new ThisExpr(tok), "_modifies"), null));
    mod.Add(new FrameExpression(tok, new MemberSelectExpr(tok, new ThisExpr(tok), "_new"), null));
    // ensures fresh(_new - old(_new));
    ens = Member_MoveNext.Ens;
    ens.Add(new AttributedExpression(new FreshExpr(tok,
      new BinaryExpr(tok, BinaryExpr.Opcode.Sub,
        new MemberSelectExpr(tok, new ThisExpr(tok), "_new"),
        new OldExpr(tok, new MemberSelectExpr(tok, new ThisExpr(tok), "_new"))))));
    // ensures null !in _new
    ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.NotIn,
      new LiteralExpr(tok),
      new MemberSelectExpr(tok, new ThisExpr(tok), "_new"))));
    // ensures more ==> this.Valid();
    valid_call = new FunctionCallExpr(tok, "Valid", new ThisExpr(tok), tok, tok, new List<ActualBinding>());
    ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Imp,
      new IdentifierExpr(tok, "more"),
      valid_call)));
    // ensures this.ys == if more then old(this.ys) + [this.y] else old(this.ys);
    Contract.Assert(OutsFields.Count == OutsHistoryFields.Count);
    for (int i = 0; i < OutsFields.Count; i++) {
      var y = OutsFields[i];
      var ys = OutsHistoryFields[i];
      var ite = new ITEExpr(tok, false, new IdentifierExpr(tok, "more"),
        new BinaryExpr(tok, BinaryExpr.Opcode.Add,
          new OldExpr(tok, new MemberSelectExpr(tok, new ThisExpr(tok), ys.Name)),
          new SeqDisplayExpr(tok, new List<Expression>() { new MemberSelectExpr(tok, new ThisExpr(tok), y.Name) })),
        new OldExpr(tok, new MemberSelectExpr(tok, new ThisExpr(tok), ys.Name)));
      var eq = new BinaryExpr(tok, BinaryExpr.Opcode.Eq, new MemberSelectExpr(tok, new ThisExpr(tok), ys.Name), ite);
      ens.Add(new AttributedExpression(eq));
    }
    // ensures more ==> YieldEnsures;
    foreach (var ye in YieldEnsures) {
      ens.Add(new AttributedExpression(
        new BinaryExpr(tok, BinaryExpr.Opcode.Imp, new IdentifierExpr(tok, "more"), ye.E)
      ));
    }
    // ensures !more ==> Ensures;
    foreach (var e in Ensures) {
      ens.Add(new AttributedExpression(new BinaryExpr(tok, BinaryExpr.Opcode.Imp,
        new UnaryOpExpr(tok, UnaryOpExpr.Opcode.Not, new IdentifierExpr(tok, "more")),
        e.E)
      ));
    }
    // decreases this._decreases0, this._decreases1, ...;
    Contract.Assert(Decreases.Expressions.Count == DecreasesFields.Count);
    for (int i = 0; i < Decreases.Expressions.Count; i++) {
      var p = Decreases.Expressions[i];
      Member_MoveNext.Decreases.Expressions.Add(new MemberSelectExpr(p.tok, new ThisExpr(p.tok), DecreasesFields[i].Name));
    }
    Member_MoveNext.Decreases.Attributes = Decreases.Attributes;
  }

  public void Resolve(Resolver resolver) {
    // register the names of the implicit members
    var members = new Dictionary<string, MemberDecl>();
    resolver.classMembers.Add(this, members);

    // First, register the iterator's in- and out-parameters as readonly fields
    foreach (var p in Ins) {
      if (members.ContainsKey(p.Name)) {
        resolver.reporter.Error(MessageSource.Resolver, p,
          "Name of in-parameter is used by another member of the iterator: {0}", p.Name);
      } else {
        var field = new SpecialField(p.RangeToken, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, false,
          false, p.Type, null);
        field.EnclosingClass = this; // resolve here
        field.InheritVisibility(this);
        members.Add(p.Name, field);
        Members.Add(field);
      }
    }

    var nonDuplicateOuts = new List<Formal>();
    foreach (var p in Outs) {
      if (members.ContainsKey(p.Name)) {
        resolver.reporter.Error(MessageSource.Resolver, p,
          "Name of yield-parameter is used by another member of the iterator: {0}", p.Name);
      } else {
        nonDuplicateOuts.Add(p);
        var field = new SpecialField(p.RangeToken, p.Name, SpecialField.ID.UseIdParam, p.CompileName, p.IsGhost, true,
          true, p.Type, null);
        field.EnclosingClass = this; // resolve here
        field.InheritVisibility(this);
        OutsFields.Add(field);
        members.Add(p.Name, field);
        Members.Add(field);
      }
    }

    foreach (var p in nonDuplicateOuts) {
      var nm = p.Name + "s";
      if (members.ContainsKey(nm)) {
        resolver.reporter.Error(MessageSource.Resolver, p.tok,
          "Name of implicit yield-history variable '{0}' is already used by another member of the iterator",
          p.Name);
        nm = p.Name + "*"; // bogus name, but at least it'll be unique
      }

      // we add some field to OutsHistoryFields, even if there was an error; the name of the field, in case of error, is not so important
      var tp = new SeqType(p.Type.NormalizeExpand());
      var field = new SpecialField(p.RangeToken, nm, SpecialField.ID.UseIdParam, nm, true, true, false, tp, null);
      field.EnclosingClass = this; // resolve here
      field.InheritVisibility(this);
      OutsHistoryFields
        .Add(field); // for now, just record this field (until all parameters have been added as members)
    }

    Contract.Assert(OutsFields.Count ==
                    OutsHistoryFields
                      .Count); // the code above makes sure this holds, even in the face of errors
    // now that already-used 'ys' names have been checked for, add these yield-history variables
    OutsHistoryFields.ForEach(f => {
      members.Add(f.Name, f);
      Members.Add(f);
    });
    // add the additional special variables as fields
    Member_Reads = new SpecialField(RangeToken, "_reads", SpecialField.ID.Reads, null, true, false, false,
      new SetType(true, resolver.builtIns.ObjectQ()), null);
    Member_Modifies = new SpecialField(RangeToken, "_modifies", SpecialField.ID.Modifies, null, true, false,
      false, new SetType(true, resolver.builtIns.ObjectQ()), null);
    Member_New = new SpecialField(RangeToken, "_new", SpecialField.ID.New, null, true, true, true,
      new SetType(true, resolver.builtIns.ObjectQ()), null);
    foreach (var field in new List<Field>() { Member_Reads, Member_Modifies, Member_New }) {
      field.EnclosingClass = this; // resolve here
      field.InheritVisibility(this);
      members.Add(field.Name, field);
      Members.Add(field);
    }

    // finally, add special variables to hold the components of the (explicit or implicit) decreases clause
    new InferDecreasesClause(resolver).FillInDefaultDecreases(this, false);
    // create the fields; unfortunately, we don't know their types yet, so we'll just insert type proxies for now
    var i = 0;
    foreach (var p in Decreases.Expressions) {
      var nm = "_decreases" + i;
      var field = new SpecialField(p.RangeToken, nm, SpecialField.ID.UseIdParam, nm, true, false, false,
        new InferredTypeProxy(), null);
      field.EnclosingClass = this; // resolve here
      field.InheritVisibility(this);
      DecreasesFields.Add(field);
      members.Add(field.Name, field);
      Members.Add(field);
      i++;
    }

    // Note, the typeArgs parameter to the following Method/Predicate constructors is passed in as the empty list.  What that is
    // saying is that the Method/Predicate does not take any type parameters over and beyond what the enclosing type (namely, the
    // iterator type) does.
    // --- here comes the constructor
    var init = new Constructor(RangeToken, new Name(NameNode.RangeToken, "_ctor"), false,
      new List<TypeParameter>(), Ins,
      new List<AttributedExpression>(),
      new Specification<FrameExpression>(new List<FrameExpression>(), null),
      new List<AttributedExpression>(),
      new Specification<Expression>(new List<Expression>(), null),
      null, null, null);
    // --- here comes predicate Valid()
    var valid = new Predicate(RangeToken, new Name(NameNode.RangeToken, "Valid"), false, true, false,
      new List<TypeParameter>(),
      new List<Formal>(),
      null,
      new List<AttributedExpression>(),
      new List<FrameExpression>(),
      new List<AttributedExpression>(),
      new Specification<Expression>(new List<Expression>(), null),
      null, Predicate.BodyOriginKind.OriginalOrInherited, null, null, null, null);
    // --- here comes method MoveNext
    var moveNext = new Method(RangeToken, new Name(NameNode.RangeToken, "MoveNext"), false, false,
      new List<TypeParameter>(),
      new List<Formal>(), new List<Formal>() { new Formal(tok, "more", Type.Bool, false, false, null) },
      new List<AttributedExpression>(),
      new Specification<FrameExpression>(new List<FrameExpression>(), null),
      new List<AttributedExpression>(),
      new Specification<Expression>(new List<Expression>(), null),
      null, Attributes.Find(Attributes, "print"), null);
    // add these implicit members to the class
    init.EnclosingClass = this;
    init.InheritVisibility(this);
    valid.EnclosingClass = this;
    valid.InheritVisibility(this);
    moveNext.EnclosingClass = this;
    moveNext.InheritVisibility(this);
    HasConstructor = true;
    Member_Init = init;
    Member_Valid = valid;
    Member_MoveNext = moveNext;
    if (members.TryGetValue(init.Name, out var member)) {
      resolver.reporter.Error(MessageSource.Resolver, member.tok,
        "member name '{0}' is already predefined for this iterator", init.Name);
    } else {
      members.Add(init.Name, init);
      Members.Add(init);
    }

    // If the name of the iterator is "Valid" or "MoveNext", one of the following will produce an error message.  That
    // error message may not be as clear as it could be, but the situation also seems unlikely to ever occur in practice.
    if (members.TryGetValue("Valid", out member)) {
      resolver.reporter.Error(MessageSource.Resolver, member.tok,
        "member name 'Valid' is already predefined for iterators");
    } else {
      members.Add(valid.Name, valid);
      Members.Add(valid);
    }

    if (members.TryGetValue("MoveNext", out member)) {
      resolver.reporter.Error(MessageSource.Resolver, member.tok,
        "member name 'MoveNext' is already predefined for iterators");
    } else {
      members.Add(moveNext.Name, moveNext);
      Members.Add(moveNext);
    }
  }


  protected override string GetTriviaContainingDocstring() {
    IToken lastClosingParenthesis = null;
    foreach (var token in OwnedTokens) {
      if (token.val == ")") {
        lastClosingParenthesis = token;
      }
    }

    if (lastClosingParenthesis != null && lastClosingParenthesis.TrailingTrivia.Trim() != "") {
      return lastClosingParenthesis.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}
