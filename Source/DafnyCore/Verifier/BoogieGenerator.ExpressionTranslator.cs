using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Dafny;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using static Microsoft.Dafny.Util;

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {
    public partial class ExpressionTranslator {
      private DafnyOptions options;

      // HeapExpr == null ==> translation of pure (no-heap) expression
      readonly Boogie.Expr _the_heap_expr;
      public Boogie.Expr HeapExpr {
        // The increment of Statistics_HeapUses in the following line is a hack and not entirely a good idea.
        // Not only does one need to be careful not to mention HeapExpr in contracts (in particular, in ObjectInvariant()
        // below), but also, the debugger may invoke HeapExpr and that will cause an increment as well.
        get { Statistics_HeapUses++; return _the_heap_expr; }
      }

      public Boogie.Expr HeapExprForArrow(Type arrowType) {
        if (arrowType.IsArrowTypeWithoutReadEffects) {
          return BoogieGenerator.NewOneHeapExpr(arrowType.Origin);
        } else {
          return HeapExpr;
        }
      }

      /// <summary>
      /// Return HeapExpr as an IdentifierExpr.
      /// CAUTION: This getter should be used only if the caller "knows" that HeapExpr really is an IdentifierExpr.
      /// </summary>
      public Boogie.IdentifierExpr HeapCastToIdentifierExpr {
        get {
          Contract.Assume(HeapExpr is Boogie.IdentifierExpr);
          return (Boogie.IdentifierExpr)HeapExpr;
        }
      }

      public readonly PredefinedDecls Predef;
      public readonly BoogieGenerator BoogieGenerator;
      public readonly string This;
      public readonly string readsFrame; // the name of the context's frame variable for reading state.
                                         // May be null to indicate the context's reads frame is * and doesn't require any reads checks.
      public readonly IFrameScope scope; // lambda, function or predicate
      public readonly string modifiesFrame; // the name of the context's frame variable for writing state.
      readonly Function applyLimited_CurrentFunction;
      internal readonly FuelSetting layerInterCluster;
      internal readonly FuelSetting layerIntraCluster = null;  // a value of null says to do the same as for inter-cluster calls
      public int Statistics_CustomLayerFunctionCount = 0;
      public int Statistics_HeapAsQuantifierCount = 0;
      public int Statistics_HeapUses = 0;
      public readonly bool stripLits = false;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        // In the following line, it is important to use _the_heap_expr directly, rather than HeapExpr, because
        // the HeapExpr getter has a side effect on Statistics_HeapUses.
        Contract.Invariant(_the_heap_expr == null || _the_heap_expr is Boogie.OldExpr || _the_heap_expr is Boogie.IdentifierExpr);
        Contract.Invariant(Predef != null);
        Contract.Invariant(BoogieGenerator != null);
        Contract.Invariant(This != null);
        Contract.Invariant(modifiesFrame != null);
        Contract.Invariant(layerInterCluster != null);
        Contract.Invariant(0 <= Statistics_CustomLayerFunctionCount);
      }

      /// <summary>
      /// This is the most general constructor.  It is private and takes all the parameters.  Whenever
      /// one ExpressionTranslator is constructed from another, unchanged parameters are just copied in.
      /// </summary>
      ExpressionTranslator(BoogieGenerator boogieGenerator, PredefinedDecls predef, Boogie.Expr heap, string thisVar,
        Function applyLimitedCurrentFunction, FuelSetting layerInterCluster, FuelSetting layerIntraCluster, IFrameScope scope,
        string readsFrame, string modifiesFrame, bool stripLits) {

        Contract.Requires(boogieGenerator != null);
        Contract.Requires(predef != null);
        Contract.Requires(thisVar != null);
        Contract.Requires(readsFrame != null);
        Contract.Requires(modifiesFrame != null);

        this.BoogieGenerator = boogieGenerator;
        this.Predef = predef;
        this._the_heap_expr = heap;
        this.This = thisVar;
        this.applyLimited_CurrentFunction = applyLimitedCurrentFunction;
        this.layerInterCluster = layerInterCluster;
        if (layerIntraCluster == null) {
          this.layerIntraCluster = layerInterCluster;
        } else {
          this.layerIntraCluster = layerIntraCluster;
        }

        this.scope = scope;
        this.readsFrame = readsFrame;
        this.modifiesFrame = modifiesFrame;
        this.stripLits = stripLits;
        this.options = boogieGenerator.options;
      }

      public static Boogie.IdentifierExpr HeapIdentifierExpr(PredefinedDecls predef, Boogie.IToken heapToken) {
        return new Boogie.IdentifierExpr(heapToken, predef.HeapVarName, predef.HeapType);
      }

      public ExpressionTranslator(BoogieGenerator boogieGenerator, PredefinedDecls predef, Boogie.IToken heapToken, IFrameScope scope)
        : this(boogieGenerator, predef, HeapIdentifierExpr(predef, heapToken), scope) {
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heapToken != null);
      }

      public ExpressionTranslator(BoogieGenerator boogieGenerator, PredefinedDecls predef, Boogie.Expr heap, IFrameScope scope)
        : this(boogieGenerator, predef, heap, scope, "this") {
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(predef != null);
      }

      public ExpressionTranslator(BoogieGenerator boogieGenerator, PredefinedDecls predef, Boogie.Expr heap, Boogie.Expr oldHeap, IFrameScope scope)
        : this(boogieGenerator, predef, heap, scope, "this") {
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(predef != null);
        Contract.Requires(oldHeap != null);

        var old = new ExpressionTranslator(boogieGenerator, predef, oldHeap, scope);
        old.oldEtran = old;
        this.oldEtran = old;
      }

      public ExpressionTranslator(BoogieGenerator boogieGenerator, PredefinedDecls predef, Boogie.Expr heap, IFrameScope scope, string thisVar)
        : this(boogieGenerator, predef, heap, thisVar, null, new FuelSetting(boogieGenerator, 1), null, scope, "$_ReadsFrame", "$_ModifiesFrame", false) {
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(predef != null);
        Contract.Requires(thisVar != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, Boogie.Expr heap)
        : this(etran.BoogieGenerator, etran.Predef, heap, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, etran.scope, etran.readsFrame, etran.modifiesFrame, etran.stripLits) {
        Contract.Requires(etran != null);
      }

      public ExpressionTranslator WithReadsFrame(string newReadsFrame, IFrameScope frameScope) {
        return new ExpressionTranslator(BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, frameScope, newReadsFrame, modifiesFrame, stripLits);
      }
      public ExpressionTranslator WithReadsFrame(string newReadsFrame) {
        return new ExpressionTranslator(BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, scope, newReadsFrame, modifiesFrame, stripLits);
      }

      public ExpressionTranslator WithModifiesFrame(string newModifiesFrame) {
        return new ExpressionTranslator(BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, scope, readsFrame, newModifiesFrame, stripLits);
      }

      internal IOrigin GetToken(Expression expression) {
        return BoogieGenerator.GetToken(expression);
      }

      ExpressionTranslator oldEtran;
      public ExpressionTranslator Old {
        get {
          Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

          if (oldEtran == null) {
            oldEtran = new ExpressionTranslator(BoogieGenerator, Predef, new Boogie.OldExpr(HeapExpr.tok, HeapExpr), This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, scope, readsFrame, modifiesFrame, stripLits);
            oldEtran.oldEtran = oldEtran;
          }
          return oldEtran;
        }
      }

      public ExpressionTranslator OldAt(Label/*?*/ label) {
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);
        if (label == null) {
          return Old;
        }
        var heapAt = new Boogie.IdentifierExpr(Token.NoToken, "$Heap_at_" + label.AssignUniqueId(BoogieGenerator.CurrentIdGenerator), Predef.HeapType);
        return new ExpressionTranslator(BoogieGenerator, Predef, heapAt, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, scope, readsFrame, modifiesFrame, stripLits);
      }

      public bool UsesOldHeap {
        get {
          return HeapExpr is Boogie.OldExpr || (HeapExpr is Boogie.IdentifierExpr ide && ide.Name.StartsWith("$Heap_at_"));
        }
      }

      public ExpressionTranslator WithLayer(Boogie.Expr layerArgument) {
        // different layer and 0 fuel amount.
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, null, new FuelSetting(BoogieGenerator, 0, layerArgument), new FuelSetting(BoogieGenerator, 0, layerArgument), readsFrame, modifiesFrame, stripLits);
      }

      internal ExpressionTranslator WithCustomFuelSetting(CustomFuelSettings customSettings) {
        // Use the existing layers but with some per-function customizations
        Contract.Requires(customSettings != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, null, layerInterCluster.WithContext(customSettings), layerIntraCluster.WithContext(customSettings), readsFrame, modifiesFrame, stripLits);
      }

      public ExpressionTranslator ReplaceLayer(Boogie.Expr layerArgument) {
        // different layer with same fuel amount.
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.WithLayer(layerArgument), layerIntraCluster.WithLayer(layerArgument), readsFrame, modifiesFrame, stripLits);
      }

      public ExpressionTranslator WithNoLits() {
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);
        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, readsFrame, modifiesFrame, true);
      }

      public ExpressionTranslator LimitedFunctions(Function applyLimited_CurrentFunction, Boogie.Expr layerArgument) {
        Contract.Requires(applyLimited_CurrentFunction != null);
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, /* layerArgument */ layerInterCluster, new FuelSetting(BoogieGenerator, 0, layerArgument), readsFrame, modifiesFrame, stripLits);
      }

      public ExpressionTranslator LayerOffset(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.Offset(offset), layerIntraCluster, readsFrame, modifiesFrame, stripLits);
      }

      public ExpressionTranslator DecreaseFuel(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, BoogieGenerator, Predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.Decrease(offset), layerIntraCluster, readsFrame, modifiesFrame, stripLits);
      }

      private static ExpressionTranslator CloneExpressionTranslator(ExpressionTranslator orig,
        BoogieGenerator boogieGenerator, PredefinedDecls predef, Boogie.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, FuelSetting layerInterCluster, FuelSetting layerIntraCluster, string readsFrame, string modifiesFrame, bool stripLits) {
        var et = new ExpressionTranslator(boogieGenerator, predef, heap, thisVar, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, orig.scope, readsFrame, modifiesFrame, stripLits);
        if (orig.oldEtran != null) {
          var etOld = new ExpressionTranslator(boogieGenerator, predef, orig.Old.HeapExpr, thisVar, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, orig.scope, readsFrame, modifiesFrame, stripLits);
          etOld.oldEtran = etOld;
          et.oldEtran = etOld;
        }
        return et;
      }

      public Boogie.IdentifierExpr ReadsFrame(IOrigin tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>().Type != null);

        if (readsFrame == null) {
          throw new ArgumentException();
        }
        return Frame(tok, readsFrame);
      }

      public Boogie.IdentifierExpr ModifiesFrame(IOrigin tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>().Type != null);

        return Frame(tok, modifiesFrame);
      }

      private Boogie.IdentifierExpr Frame(IOrigin tok, string frameName) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>().Type != null);

        Boogie.Type ty = new Boogie.MapType(tok, [], [Predef.RefType, Predef.FieldName(tok)], Boogie.Type.Bool);
        return new Boogie.IdentifierExpr(tok, frameName, ty);
      }

      public Boogie.IdentifierExpr ArbitraryBoxValue() {
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        return new Boogie.IdentifierExpr(Token.NoToken, "$ArbitraryBoxValue", Predef.BoxType);
      }
      public Boogie.Expr ArbitraryValue(Type type) {
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);
        var bx = ArbitraryBoxValue();
        if (!ModeledAsBoxType(type)) {
          return BoogieGenerator.FunctionCall(Token.NoToken, BuiltinFunction.Unbox, BoogieGenerator.TrType(type), bx);
        } else {
          return bx;
        }
      }

      public Expression GetSubstitutedBody(LetExpr e) {
        Contract.Requires(e != null);
        Contract.Requires(e.Exact);
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < e.LHSs.Count; i++) {
          BoogieGenerator.AddCasePatternVarSubstitutions(e.LHSs[i], TrExpr(e.RHSs[i]), substMap);
        }
        return BoogieGenerator.Substitute(e.Body, null, substMap);
      }

      public Expr MaybeLit(Expr expr, Boogie.Type type) {
        return stripLits ? expr : BoogieGenerator.Lit(expr, type);
      }

      public Expr MaybeLit(Expr expr) {
        return stripLits ? expr : BoogieGenerator.Lit(expr);
      }

      /// <summary>
      /// Translates Dafny expression "expr" into a Boogie expression.  If the type of "expr" can be a boolean, then the
      /// token (source location) of the resulting expression is filled in (it wouldn't hurt if the token were always
      /// filled in, but it is really necessary for anything that may show up in a Boogie assert, since that location may
      /// then show up in an error message).
      /// </summary>
      public Boogie.Expr TrExpr(Expression expr) {
        Contract.Requires(expr != null);
        Contract.Requires(Predef != null);

        switch (expr) {
          case LiteralExpr literalExpr: {
              LiteralExpr e = literalExpr;
              if (e.Value == null) {
                return Predef.Null;
              } else if (e.Value is bool) {
                return MaybeLit(new Boogie.LiteralExpr(GetToken(e), (bool)e.Value));
              } else if (e is CharLiteralExpr) {
                // we expect e.Value to be a string representing exactly one char
                Boogie.Expr rawElement = null;  // assignment to please compiler's definite assignment rule
                foreach (var ch in Util.UnescapedCharacters(options, (string)e.Value, false)) {
                  Contract.Assert(rawElement == null);  // we should get here only once
                  rawElement = BoogieGenerator.FunctionCall(GetToken(literalExpr), BuiltinFunction.CharFromInt, null, Boogie.Expr.Literal(ch));
                }
                Contract.Assert(rawElement != null);  // there should have been an iteration of the loop above
                return MaybeLit(rawElement, Predef.CharType);
              } else if (e is StringLiteralExpr) {
                var str = (StringLiteralExpr)e;
                Boogie.Expr seq = BoogieGenerator.FunctionCall(GetToken(literalExpr), BuiltinFunction.SeqEmpty, Predef.BoxType);
                foreach (var ch in Util.UnescapedCharacters(options, (string)e.Value, str.IsVerbatim)) {
                  var rawElement = BoogieGenerator.FunctionCall(GetToken(literalExpr), BuiltinFunction.CharFromInt, null, Boogie.Expr.Literal(ch));
                  Boogie.Expr elt = BoxIfNecessary(GetToken(literalExpr), rawElement, Type.Char);
                  seq = BoogieGenerator.FunctionCall(GetToken(literalExpr), BuiltinFunction.SeqBuild, Predef.BoxType, seq, elt);
                }
                return MaybeLit(seq, BoogieGenerator.TrType(new SeqType(Type.Char)));
              } else if (e.Value is BigInteger) {
                var n = Microsoft.BaseTypes.BigNum.FromBigInt((BigInteger)e.Value);
                if (e.Type.NormalizeToAncestorType() is BitvectorType bitvectorType) {
                  return MaybeLit(BoogieGenerator.BplBvLiteralExpr(GetToken(e), n, bitvectorType));
                } else if (e.Type.IsBigOrdinalType) {
                  var fromNat = FunctionCall(GetToken(literalExpr), "ORD#FromNat", Predef.BigOrdinalType, Boogie.Expr.Literal(n));
                  return MaybeLit(fromNat, Predef.BigOrdinalType);
                } else {
                  return MaybeLit(Boogie.Expr.Literal(n));
                }
              } else if (e.Value is BaseTypes.BigDec) {
                return MaybeLit(Boogie.Expr.Literal((BaseTypes.BigDec)e.Value));
              } else {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
              }
            }
          case ThisExpr:
            return new Boogie.IdentifierExpr(GetToken(expr), This, BoogieGenerator.TrType(expr.Type));
          case IdentifierExpr identifierExpr: {
              IdentifierExpr e = identifierExpr;
              Contract.Assert(e.Var != null);
              return BoogieGenerator.TrVar(GetToken(identifierExpr), e.Var);
            }
          case BoogieWrapper wrapper: {
              var e = wrapper;
              return e.Expr;
            }
          case BoogieFunctionCall call: {
              var e = call;
              var id = new Boogie.IdentifierExpr(GetToken(e), e.FunctionName, BoogieGenerator.TrType(e.Type));
              var args = new List<Boogie.Expr>();
              foreach (var arg in e.TyArgs) {
                args.Add(BoogieGenerator.TypeToTy(arg));
              }
              if (e.UsesHeap) {
                args.Add(HeapExpr);
              }
              if (e.UsesOldHeap) {
                args.Add(Old.HeapExpr);
              }
              foreach (var heapAtLabel in e.HeapAtLabels) {
                var bv = BplBoundVar("$Heap_at_" + heapAtLabel.AssignUniqueId(BoogieGenerator.CurrentIdGenerator), BoogieGenerator.Predef.HeapType, out var ve);
                args.Add(ve);
              }
              foreach (var arg in e.Args) {
                args.Add(TrExpr(arg));
              }
              return new Boogie.NAryExpr(GetToken(e), new Boogie.FunctionCall(id), args);
            }
          case SetDisplayExpr displayExpr: {
              SetDisplayExpr e = displayExpr;
              Boogie.Expr s = BoogieGenerator.FunctionCall(GetToken(displayExpr), e.Finite ? BuiltinFunction.SetEmpty : BuiltinFunction.ISetEmpty, Predef.BoxType);
              var isLit = true;
              foreach (Expression ee in e.Elements) {
                var rawElement = TrExpr(ee);
                isLit = isLit && BoogieGenerator.IsLit(rawElement);
                Boogie.Expr ss = BoxIfNecessary(GetToken(displayExpr), rawElement, cce.NonNull(ee.Type));
                s = BoogieGenerator.FunctionCall(GetToken(displayExpr), e.Finite ? BuiltinFunction.SetUnionOne : BuiltinFunction.ISetUnionOne, Predef.BoxType, s, ss);
              }
              if (isLit) {
                // Lit-lifting: All elements are lit, so the set is Lit too
                s = MaybeLit(s, Predef.BoxType);
              }
              return s;
            }
          case MultiSetDisplayExpr displayExpr: {
              MultiSetDisplayExpr e = displayExpr;
              Boogie.Expr s = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetEmpty, Predef.BoxType);
              var isLit = true;
              foreach (Expression ee in e.Elements) {
                var rawElement = TrExpr(ee);
                isLit = isLit && BoogieGenerator.IsLit(rawElement);
                Boogie.Expr ss = BoxIfNecessary(GetToken(displayExpr), rawElement, cce.NonNull(ee.Type));
                s = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.MultiSetUnionOne, Predef.BoxType, s, ss);
              }
              if (isLit) {
                // Lit-lifting: All elements are lit, so the multiset is Lit too
                s = MaybeLit(s, Predef.BoxType);
              }
              return s;
            }
          case SeqDisplayExpr displayExpr: {
              SeqDisplayExpr e = displayExpr;
              // Note: a LiteralExpr(string) is really another kind of SeqDisplayExpr
              Boogie.Expr s = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.SeqEmpty, Predef.BoxType);
              var isLit = true;
              foreach (Expression ee in e.Elements) {
                var rawElement = TrExpr(ee);
                isLit = isLit && BoogieGenerator.IsLit(rawElement);
                Boogie.Expr elt = BoxIfNecessary(GetToken(displayExpr), rawElement, ee.Type);
                s = BoogieGenerator.FunctionCall(GetToken(displayExpr), BuiltinFunction.SeqBuild, Predef.BoxType, s, elt);
              }
              if (isLit) {
                // Lit-lifting: All elements are lit, so the sequence is Lit too
                s = MaybeLit(s, Predef.BoxType);
              }
              return s;
            }
          case MapDisplayExpr displayExpr: {
              MapDisplayExpr e = displayExpr;
              Boogie.Type maptype = e.Finite ? Predef.MapType : Predef.IMapType;
              Boogie.Expr s = BoogieGenerator.FunctionCall(GetToken(displayExpr), e.Finite ? BuiltinFunction.MapEmpty : BuiltinFunction.IMapEmpty, Predef.BoxType);
              var isLit = true;
              foreach (MapDisplayEntry p in e.Elements) {
                var rawA = TrExpr(p.A);
                var rawB = TrExpr(p.B);
                isLit = isLit && BoogieGenerator.IsLit(rawA) && BoogieGenerator.IsLit(rawB);
                Boogie.Expr elt = BoxIfNecessary(GetToken(displayExpr), rawA, cce.NonNull(p.A.Type));
                Boogie.Expr elt2 = BoxIfNecessary(GetToken(displayExpr), rawB, cce.NonNull(p.B.Type));
                s = FunctionCall(GetToken(displayExpr), e.Finite ? "Map#Build" : "IMap#Build", maptype, s, elt, elt2);
              }
              if (isLit) {
                // Lit-lifting: All keys and values are lit, so the map is Lit too
                s = MaybeLit(s, Predef.BoxType);
              }
              return s;
            }
          case MemberSelectExpr selectExpr: {
              var e = selectExpr;
              return e.MemberSelectCase(
                field => {
                  var useSurrogateLocal = BoogieGenerator.inBodyInitContext && Expression.AsThis(e.Obj) != null && !field.IsInstanceIndependentConstant;
                  var fType = BoogieGenerator.TrType(field.Type);
                  if (useSurrogateLocal) {
                    return new Boogie.IdentifierExpr(GetToken(expr), BoogieGenerator.SurrogateName(field), fType);
                  } else if (field is ConstantField) {
                    var typeMap = e.TypeArgumentSubstitutionsWithParents();
                    var args = GetTypeParams(field.EnclosingClass).ConvertAll(tp => BoogieGenerator.TypeToTy(typeMap[tp]));
                    Boogie.Expr result;
                    if (field.IsStatic) {
                      result = new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(BoogieGenerator.GetReadonlyField(field)), args);
                    } else {
                      Boogie.Expr obj = BoogieGenerator.BoxifyForTraitParent(e.Origin, TrExpr(e.Obj), e.Member, e.Obj.Type);
                      args.Add(obj);
                      result = new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(BoogieGenerator.GetReadonlyField(field)), args);
                    }
                    result = BoogieGenerator.CondApplyUnbox(GetToken(expr), result, field.Type, expr.Type);
                    return result;
                  } else {
                    Boogie.Expr obj = TrExpr(e.Obj);
                    Boogie.Expr result;
                    if (field.IsMutable) {
                      var tok = GetToken(expr);
                      result = BoogieGenerator.ReadHeap(tok, HeapExpr, obj, new Boogie.IdentifierExpr(GetToken(expr), BoogieGenerator.GetField(field)));
                      result = fType == Predef.BoxType ? result : BoogieGenerator.ApplyUnbox(tok, result, fType);
                      return BoogieGenerator.CondApplyUnbox(tok, result, field.Type, expr.Type);
                    } else {
                      result = new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(BoogieGenerator.GetReadonlyField(field)),
                        new List<Boogie.Expr> { obj });
                      result = BoogieGenerator.CondApplyUnbox(GetToken(expr), result, field.Type, expr.Type);
                      if (BoogieGenerator.IsLit(obj)) {
                        result = MaybeLit(result, BoogieGenerator.TrType(expr.Type));
                      }
                      return result;
                    }
                  }
                },
                fn => {
                  var typeMap = e.TypeArgumentSubstitutionsWithParents();
                  var args = GetTypeParams(fn).ConvertAll(tp => BoogieGenerator.TypeToTy(typeMap[tp]));
                  if (fn.IsFuelAware()) {
                    args.Add(this.layerInterCluster.GetFunctionFuel(fn));
                  }
                  if (fn.IsOpaque || fn.IsMadeImplicitlyOpaque(options)) {
                    args.Add(BoogieGenerator.GetRevealConstant(fn));
                  }
                  if (fn is TwoStateFunction) {
                    args.Add(Old.HeapExpr);
                  }
                  if (!fn.IsStatic) {
                    Boogie.Expr obj = BoogieGenerator.BoxifyForTraitParent(e.Origin, TrExpr(e.Obj), e.Member, e.Obj.Type);
                    args.Add(obj);
                  }
                  return FunctionCall(GetToken(e), BoogieGenerator.FunctionHandle(fn), Predef.HandleType, args);
                });
            }
          case SeqSelectExpr selectExpr: {
              SeqSelectExpr e = selectExpr;
              Boogie.Expr seq = TrExpr(e.Seq);
              var seqType = e.Seq.Type.NormalizeToAncestorType();
              Type elmtType = null;
              Type domainType = null;
              Contract.Assert(seqType != null);  // the expression has been successfully resolved
              if (seqType.IsArrayType) {
                domainType = Type.Int;
                elmtType = UserDefinedType.ArrayElementType(seqType);
              } else if (seqType is SeqType) {
                domainType = Type.Int;
                elmtType = ((SeqType)seqType).Arg;
              } else if (seqType is MapType) {
                domainType = ((MapType)seqType).Domain;
                elmtType = ((MapType)seqType).Range;
              } else if (seqType is MultiSetType) {
                domainType = ((MultiSetType)seqType).Arg;
                elmtType = Type.Int;
              } else { Contract.Assert(false); }
              Boogie.Type elType = BoogieGenerator.TrType(elmtType);
              Boogie.Type dType = BoogieGenerator.TrType(domainType);
              Boogie.Expr e0 = e.E0 == null ? null : TrExpr(e.E0);
              if (e0 != null && e.E0.Type.IsBitVectorType) {
                e0 = BoogieGenerator.ConvertExpression(GetToken(e.E0), e0, e.E0.Type, Type.Int);
              }
              Boogie.Expr e1 = e.E1 == null ? null : TrExpr(e.E1);
              if (e1 != null && e.E1.Type.IsBitVectorType) {
                e1 = BoogieGenerator.ConvertExpression(GetToken(e.E1), e1, e.E1.Type, Type.Int);
              }
              if (e.SelectOne) {
                Contract.Assert(e1 == null);
                Boogie.Expr x;
                if (seqType.IsArrayType) {
                  Boogie.Expr fieldName = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.IndexField, null, e0);
                  x = BoogieGenerator.ReadHeap(GetToken(selectExpr), HeapExpr, TrExpr(e.Seq), fieldName);
                } else if (seqType is SeqType) {
                  x = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.SeqIndex, Predef.BoxType, seq, e0);
                } else if (seqType is MapType) {
                  bool finite = ((MapType)seqType).Finite;
                  var f = finite ? BuiltinFunction.MapElements : BuiltinFunction.IMapElements;
                  x = BoogieGenerator.FunctionCall(GetToken(selectExpr), f, finite ? Predef.MapType : Predef.IMapType, seq);
                  x = Boogie.Expr.Select(x, BoxIfNecessary(GetToken(e), e0, domainType));
                } else if (seqType is MultiSetType) {
                  x = BoogieGenerator.MultisetMultiplicity(GetToken(selectExpr), TrExpr(e.Seq), BoxIfNecessary(GetToken(selectExpr), e0, domainType));
                } else { Contract.Assert(false); x = null; }
                if (!ModeledAsBoxType(elmtType) && !(seqType is MultiSetType)) {
                  x = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.Unbox, elType, x);
                }
                return x;
              } else {
                if (seqType.IsArrayType) {
                  seq = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.SeqFromArray, elType, HeapExpr, seq);
                }
                var isLit = BoogieGenerator.IsLit(seq);
                if (e1 != null) {
                  isLit = isLit && BoogieGenerator.IsLit(e1);
                  seq = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.SeqTake, elType, seq, e1);
                }
                if (e0 != null) {
                  isLit = isLit && BoogieGenerator.IsLit(e0);
                  seq = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.SeqDrop, elType, seq, e0);
                }
                // if e0 == null && e1 == null, then we have the identity operation seq[..] == seq;
                if (isLit && (e0 != null || e1 != null)) {
                  // Lit-lift the expression
                  seq = MaybeLit(seq, BoogieGenerator.TrType(selectExpr.Type));
                }
                return seq;
              }
            }
          case SeqUpdateExpr updateExpr: {
              SeqUpdateExpr e = updateExpr;
              Boogie.Expr seq = TrExpr(e.Seq);
              var seqType = e.Seq.Type.NormalizeToAncestorType();
              if (seqType is SeqType) {
                Boogie.Expr index = TrExpr(e.Index);
                index = BoogieGenerator.ConvertExpression(GetToken(e.Index), index, e.Index.Type, Type.Int);
                Boogie.Expr val = BoxIfNecessary(GetToken(updateExpr), TrExpr(e.Value), e.Value.Type);
                return BoogieGenerator.FunctionCall(GetToken(updateExpr), BuiltinFunction.SeqUpdate, Predef.BoxType, seq, index, val);
              } else if (seqType is MapType) {
                MapType mt = (MapType)seqType;
                Boogie.Type maptype = mt.Finite ? Predef.MapType : Predef.IMapType;
                Boogie.Expr index = BoxIfNecessary(GetToken(updateExpr), TrExpr(e.Index), mt.Domain);
                Boogie.Expr val = BoxIfNecessary(GetToken(updateExpr), TrExpr(e.Value), mt.Range);
                return FunctionCall(GetToken(updateExpr), mt.Finite ? "Map#Build" : "IMap#Build", maptype, seq, index, val);
              } else if (seqType is MultiSetType) {
                Type elmtType = cce.NonNull((MultiSetType)seqType).Arg;
                Boogie.Expr index = BoxIfNecessary(GetToken(updateExpr), TrExpr(e.Index), elmtType);
                Boogie.Expr val = TrExpr(e.Value);
                return BoogieGenerator.UpdateMultisetMultiplicity(GetToken(updateExpr), seq, index, val);
              } else {
                Contract.Assert(false);
                throw new cce.UnreachableException();
              }
            }
          case MultiSelectExpr selectExpr: {
              MultiSelectExpr e = selectExpr;
              Type elmtType = UserDefinedType.ArrayElementType(e.Array.Type); ;
              Boogie.Type elType = BoogieGenerator.TrType(elmtType);

              Boogie.Expr fieldName = GetArrayIndexFieldName(GetToken(selectExpr), e.Indices);
              Boogie.Expr x = BoogieGenerator.ReadHeap(GetToken(selectExpr), HeapExpr, TrExpr(e.Array), fieldName);
              if (!ModeledAsBoxType(elmtType)) {
                x = BoogieGenerator.FunctionCall(GetToken(selectExpr), BuiltinFunction.Unbox, elType, x);
              }
              return x;
            }
          case ApplyExpr applyExpr: {
              ApplyExpr e = applyExpr;
              int arity = e.Args.Count;
              var tt = e.Function.Type.AsArrowType;
              Contract.Assert(tt != null);
              Contract.Assert(tt.Arity == arity);

              {
                // optimisation: if this could have just as well been a FunctionCallExpr, call it as such!
                var con = e.Function as ConcreteSyntaxExpression;
                var recv = con == null ? e.Function : con.Resolved;
                var mem = recv as MemberSelectExpr;
                var fn = mem == null ? null : mem.Member as Function;
                if (fn != null) {
                  return TrExpr(new FunctionCallExpr(e.Origin, fn.NameNode, mem.Obj, e.Origin, e.CloseParen, e.Args) {
                    Function = fn,
                    Type = e.Type,
                    TypeApplication_AtEnclosingClass = mem.TypeApplicationAtEnclosingClass,
                    TypeApplication_JustFunction = mem.TypeApplicationJustMember
                  });
                }
              }

              Func<Expression, Boogie.Expr> TrArg = arg => BoogieGenerator.BoxIfNotNormallyBoxed(arg.Origin, TrExpr(arg), arg.Type);

              var applied = FunctionCall(GetToken(applyExpr), BoogieGenerator.Apply(arity), Predef.BoxType,
                Concat(Map(tt.TypeArgs, BoogieGenerator.TypeToTy),
                  Cons(HeapExprForArrow(e.Function.Type), Cons(TrExpr(e.Function), e.Args.ConvertAll(arg => TrArg(arg))))));

              return BoogieGenerator.UnboxUnlessInherentlyBoxed(applied, tt.Result);
            }
          case FunctionCallExpr callExpr: {
              FunctionCallExpr e = callExpr;
              if (e.Function is SpecialFunction) {
                return TrExprSpecialFunctionCall(e);
              } else {
                Boogie.Expr layerArgument;
                Boogie.Expr revealArgument;
                var etran = this;
                if (e.Function.ContainsQuantifier && BoogieGenerator.stmtContext == StmtType.ASSUME && BoogieGenerator.adjustFuelForExists) {
                  // we need to increase fuel functions that contain quantifier expr in the assume context.
                  etran = etran.LayerOffset(1);
                  BoogieGenerator.adjustFuelForExists = false;
                }
                if (e.Function.IsFuelAware()) {
                  Statistics_CustomLayerFunctionCount++;
                  ModuleDefinition module = e.Function.EnclosingClass.EnclosingModuleDefinition;
                  if (etran.applyLimited_CurrentFunction != null &&
                      etran.layerIntraCluster != null &&
                      ModuleDefinition.InSameSCC(e.Function, applyLimited_CurrentFunction)) {
                    layerArgument = etran.layerIntraCluster.GetFunctionFuel(e.Function);
                  } else {
                    layerArgument = etran.layerInterCluster.GetFunctionFuel(e.Function);
                  }
                } else {
                  layerArgument = null;
                }

                if (e.Function.IsOpaque || e.Function.IsMadeImplicitlyOpaque(options)) {
                  revealArgument = BoogieGenerator.GetRevealConstant(e.Function);
                } else {
                  revealArgument = null;
                }

                var ty = BoogieGenerator.TrType(e.Type);
                var id = new Boogie.IdentifierExpr(GetToken(e), e.Function.FullSanitizedName, ty);

                var args = FunctionInvocationArguments(e, layerArgument, revealArgument, false, out var argsAreLit);
                Expr result = new Boogie.NAryExpr(GetToken(e), new Boogie.FunctionCall(id), args);
                result = BoogieGenerator.CondApplyUnbox(GetToken(e), result, e.Function.ResultType, e.Type);

                bool callIsLit = argsAreLit
                                 && BoogieGenerator.FunctionBodyIsAvailable(e.Function, BoogieGenerator.currentModule, BoogieGenerator.currentScope)
                                 && !e.Function.Reads.Expressions.Any(); // Function could depend on external values
                if (callIsLit) {
                  result = MaybeLit(result, ty);
                }

                return result;
              }
            }
          case DatatypeValue value: {
              DatatypeValue dtv = value;
              Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
              List<Boogie.Expr> args = [];

              bool argsAreLit = true;
              for (int i = 0; i < dtv.Arguments.Count; i++) {
                Expression arg = dtv.Arguments[i];
                Type t = dtv.Ctor.Formals[i].Type;
                var bArg = TrExpr(arg);
                argsAreLit = argsAreLit && BoogieGenerator.IsLit(bArg);
                args.Add(BoogieGenerator.AdaptBoxing(GetToken(value), bArg, cce.NonNull(arg.Type), t));
              }
              Boogie.IdentifierExpr id = new Boogie.IdentifierExpr(GetToken(dtv), dtv.Ctor.FullName, Predef.DatatypeType);
              Boogie.Expr ret = new Boogie.NAryExpr(GetToken(dtv), new Boogie.FunctionCall(id), args);
              if (argsAreLit) {
                // If all arguments are Lit, so is the whole expression
                ret = MaybeLit(ret, Predef.DatatypeType);
              }
              return ret;
            }
          case SeqConstructionExpr constructionExpr: {
              var e = constructionExpr;
              var eType = e.Type.NormalizeToAncestorType().AsSeqType.Arg.NormalizeExpand();
              var initalizerHeap = e.Initializer.Type.IsArrowType ? HeapExprForArrow(e.Initializer.Type) : HeapExpr;
              return FunctionCall(GetToken(constructionExpr), "Seq#Create", Predef.SeqType,
                BoogieGenerator.TypeToTy(eType),
                initalizerHeap,
                TrExpr(e.N),
                TrExpr(e.Initializer));
            }
          case MultiSetFormingExpr formingExpr: {
              MultiSetFormingExpr e = formingExpr;
              var eType = e.E.Type.NormalizeToAncestorType();
              if (eType is SetType setType) {
                return BoogieGenerator.FunctionCall(GetToken(formingExpr), BuiltinFunction.MultiSetFromSet, BoogieGenerator.TrType(setType.Arg), TrExpr(e.E));
              } else if (eType is SeqType seqType) {
                return BoogieGenerator.FunctionCall(GetToken(formingExpr), BuiltinFunction.MultiSetFromSeq, BoogieGenerator.TrType(seqType.Arg), TrExpr(e.E));
              } else {
                Contract.Assert(false); throw new cce.UnreachableException();
              }
            }
          case OldExpr oldExpr: {
              var e = oldExpr;
              return OldAt(e.AtLabel).TrExpr(e.Expr);
            }
          case UnchangedExpr unchangedExpr: {
              var e = unchangedExpr;
              return BoogieGenerator.FrameCondition(GetToken(e), e.Frame, false, FrameExpressionUse.Unchanged, OldAt(e.AtLabel), this, this, true);
            }
          case UnaryOpExpr opExpr: {
              var e = opExpr;
              Boogie.Expr arg = TrExpr(e.E);
              switch (e.ResolvedOp) {
                case UnaryOpExpr.ResolvedOpcode.Lit:
                  return MaybeLit(arg);
                case UnaryOpExpr.ResolvedOpcode.BVNot:
                  var bvWidth = opExpr.Type.NormalizeToAncestorType().AsBitVectorType.Width;
                  var bvType = BoogieGenerator.BplBvType(bvWidth);
                  Boogie.Expr r = FunctionCall(GetToken(opExpr), "not_bv" + bvWidth, bvType, arg);
                  if (BoogieGenerator.IsLit(arg)) {
                    r = MaybeLit(r, bvType);
                  }
                  return r;
                case UnaryOpExpr.ResolvedOpcode.BoolNot:
                  return Boogie.Expr.Unary(GetToken(opExpr), UnaryOperator.Opcode.Not, arg);
                case UnaryOpExpr.ResolvedOpcode.SeqLength:
                  Contract.Assert(e.E.Type.NormalizeToAncestorType() is SeqType);
                  return BoogieGenerator.FunctionCall(GetToken(opExpr), BuiltinFunction.SeqLength, null, arg);
                case UnaryOpExpr.ResolvedOpcode.SetCard:
                  Contract.Assert(e.E.Type.NormalizeToAncestorType() is SetType { Finite: true });
                  return BoogieGenerator.FunctionCall(GetToken(opExpr), BuiltinFunction.SetCard, null, arg);
                case UnaryOpExpr.ResolvedOpcode.MultiSetCard:
                  Contract.Assert(e.E.Type.NormalizeToAncestorType() is MultiSetType);
                  return BoogieGenerator.FunctionCall(GetToken(opExpr), BuiltinFunction.MultiSetCard, null, arg);
                case UnaryOpExpr.ResolvedOpcode.MapCard:
                  Contract.Assert(e.E.Type.NormalizeToAncestorType() is MapType { Finite: true });
                  return BoogieGenerator.FunctionCall(GetToken(opExpr), BuiltinFunction.MapCard, null, arg);
                case UnaryOpExpr.ResolvedOpcode.Fresh:
                  var freshLabel = ((FreshExpr)e).AtLabel;
                  var eeType = e.E.Type.NormalizeToAncestorType();
                  if (eeType is SetType setType) {
                    // generate:  (forall $o: ref :: { $o != null } X[Box($o)] ==> $o != null) &&
                    //            (forall $o: ref :: { X[Box($o)] } X[Box($o)] ==> !old($Heap)[$o,alloc])
                    // OR, if X[Box($o)] is rewritten into smaller parts, use the less good trigger old($Heap)[$o,alloc]
                    Boogie.Variable oVar = new Boogie.BoundVariable(GetToken(opExpr), new Boogie.TypedIdent(GetToken(opExpr), "$o", Predef.RefType));
                    Boogie.Expr o = new Boogie.IdentifierExpr(GetToken(opExpr), oVar);
                    Boogie.Expr oNotNull = Boogie.Expr.Neq(o, Predef.Null);
                    Boogie.Expr oInSet = TrInSet(GetToken(opExpr), o, e.E, setType.Arg, setType.Finite, true, out var performedInSetRewrite);
                    Boogie.Expr oNotFresh = OldAt(freshLabel).IsAlloced(GetToken(opExpr), o);
                    Boogie.Expr oIsFresh = Boogie.Expr.Not(oNotFresh);
                    Boogie.Expr notNullBody = BplImp(oInSet, oNotNull);
                    Boogie.Expr freshBody = BplImp(oInSet, oIsFresh);
                    var notNullTrigger = BplTrigger(oNotNull);
                    var notNullPred = new Boogie.ForallExpr(GetToken(opExpr), [oVar], notNullTrigger, notNullBody);
                    var freshTrigger = BplTrigger(performedInSetRewrite ? oNotFresh : oInSet);
                    var freshPred = new Boogie.ForallExpr(GetToken(opExpr), [oVar], freshTrigger, freshBody);
                    return BplAnd(notNullPred, freshPred);
                  } else if (eeType is SeqType) {
                    // generate:  (forall $i: int :: 0 <= $i && $i < Seq#Length(X) ==> Unbox(Seq#Index(X,$i)) != null && !old($Heap)[Unbox(Seq#Index(X,$i)),alloc])
                    Boogie.Variable iVar = new Boogie.BoundVariable(GetToken(opExpr), new Boogie.TypedIdent(GetToken(opExpr), "$i", Boogie.Type.Int));
                    Boogie.Expr i = new Boogie.IdentifierExpr(GetToken(opExpr), iVar);
                    Boogie.Expr iBounds = BoogieGenerator.InSeqRange(GetToken(opExpr), i, Type.Int, TrExpr(e.E), true, null, false);
                    Boogie.Expr XsubI = BoogieGenerator.FunctionCall(GetToken(opExpr), BuiltinFunction.SeqIndex, Predef.RefType, TrExpr(e.E), i);
                    XsubI = BoogieGenerator.FunctionCall(GetToken(opExpr), BuiltinFunction.Unbox, Predef.RefType, XsubI);
                    Boogie.Expr oNotFresh = OldAt(freshLabel).IsAlloced(GetToken(opExpr), XsubI);
                    Boogie.Expr oIsFresh = Boogie.Expr.Not(oNotFresh);
                    Boogie.Expr xsubiNotNull = Boogie.Expr.Neq(XsubI, Predef.Null);
                    Boogie.Expr body = BplImp(iBounds, BplAnd(xsubiNotNull, oIsFresh));
                    //TRIGGERS: Does this make sense? dafny0\SmallTests
                    // BROKEN // NEW_TRIGGER
                    //TRIG (forall $i: int :: 0 <= $i && $i < Seq#Length(Q#0) && $Unbox(Seq#Index(Q#0, $i)): ref != null ==> !read(old($Heap), $Unbox(Seq#Index(Q#0, $i)): ref, alloc))
                    return new Boogie.ForallExpr(GetToken(opExpr), [iVar], body);
                  } else {
                    // generate:  x != null && !old($Heap)[x]
                    Boogie.Expr oNull = Boogie.Expr.Neq(TrExpr(e.E), Predef.Null);
                    Boogie.Expr oIsFresh = Boogie.Expr.Not(OldAt(freshLabel).IsAlloced(GetToken(opExpr), TrExpr(e.E)));
                    return Boogie.Expr.Binary(GetToken(opExpr), BinaryOperator.Opcode.And, oNull, oIsFresh);
                  }
                case UnaryOpExpr.ResolvedOpcode.Allocated:
                  // Translate with $IsAllocBox, even if it requires boxing the argument. This has the effect of giving
                  // both the $IsAllocBox and $IsAlloc forms, because the axioms that connects these two is triggered
                  // by $IsAllocBox.
                  return BoogieGenerator.MkIsAllocBox(BoxIfNecessary(e.E.Origin, TrExpr(e.E), e.E.Type), e.E.Type, HeapExpr);
                case UnaryOpExpr.ResolvedOpcode.Assigned:
                  string name = null;
                  switch (e.E.Resolved) {
                    case IdentifierExpr ie:
                      name = ie.Var.UniqueName;
                      break;
                    case MemberSelectExpr mse:
                      if (BoogieGenerator.inBodyInitContext && Expression.AsThis(mse.Obj) != null) {
                        name = BoogieGenerator.SurrogateName(mse.Member as Field);
                      }
                      break;
                  }

                  if (name == null) {
                    return Expr.True;
                  }
                  BoogieGenerator.DefiniteAssignmentTrackers.TryGetValue(name, out var defass);
                  return defass;
                default:
                  Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
              }
            }
          case ConversionExpr conversionExpr: {
              var e = conversionExpr;
              return BoogieGenerator.ConvertExpression(GetToken(e), TrExpr(e.E), e.E.Type, e.ToType);
            }
          case TypeTestExpr testExpr: {
              var e = testExpr;
              return BoogieGenerator.GetSubrangeCheck(e.Origin, TrExpr(e.E), e.E.Type, e.ToType, e.E, null, out var _) ?? Boogie.Expr.True;
            }
          case BinaryExpr binaryExpr: {
              BinaryExpr e = binaryExpr;
              var e0Type = e.E0.Type.NormalizeToAncestorType(); // used when making decisions about what Boogie operator/functions to use
              bool isReal = e0Type.IsNumericBased(Type.NumericPersuasion.Real);
              int bvWidth = e0Type.IsBitVectorType ? e0Type.AsBitVectorType.Width : -1;  // -1 indicates "not a bitvector type"
              Boogie.Expr e0 = TrExpr(e.E0);
              if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet) {
                return TrInSet(GetToken(binaryExpr), e0, e.E1, e.E0.Type, e.E1.Type.NormalizeToAncestorType().AsSetType.Finite, false, out var pr);  // let TrInSet translate e.E1
              } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSet) {
                Boogie.Expr arg = TrInSet(GetToken(binaryExpr), e0, e.E1, e.E0.Type, e.E1.Type.NormalizeToAncestorType().AsSetType.Finite, false, out var pr);  // let TrInSet translate e.E1
                return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, arg);
              } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
                return TrInMultiSet(GetToken(binaryExpr), e0, e.E1, e.E0.Type, false); // let TrInMultiSet translate e.E1
              } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInMultiSet) {
                Boogie.Expr arg = TrInMultiSet(GetToken(binaryExpr), e0, e.E1, e.E0.Type, false);  // let TrInMultiSet translate e.E1
                return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, arg);
              }
              Boogie.Expr e1 = TrExpr(e.E1);
              BinaryOperator.Opcode bOpcode;
              Boogie.Type typ;
              var oe0 = e0;
              var oe1 = e1;
              var lit0 = BoogieGenerator.GetLit(e0);
              var lit1 = BoogieGenerator.GetLit(e1);
              bool liftLit = BoogieGenerator.IsLit(e0) && BoogieGenerator.IsLit(e1);
              // NOTE(namin): We usually avoid keeping literals, because their presence might mess up triggers that do not expect them.
              //              Still for equality-related operations, it's useful to keep them instead of lifting them, so that they can be propagated.
              bool keepLits = false;
              if (lit0 != null) {
                e0 = lit0;
              }
              if (lit1 != null) {
                e1 = lit1;
              }
              switch (e.ResolvedOp) {
                case BinaryExpr.ResolvedOpcode.Iff:
                  typ = Boogie.Type.Bool;
                  bOpcode = BinaryOperator.Opcode.Iff; break;
                case BinaryExpr.ResolvedOpcode.Imp:
                  typ = Boogie.Type.Bool;
                  bOpcode = BinaryOperator.Opcode.Imp; break;
                case BinaryExpr.ResolvedOpcode.And:
                  typ = Boogie.Type.Bool;
                  bOpcode = BinaryOperator.Opcode.And; break;
                case BinaryExpr.ResolvedOpcode.Or:
                  typ = Boogie.Type.Bool;
                  bOpcode = BinaryOperator.Opcode.Or; break;

                case BinaryExpr.ResolvedOpcode.EqCommon:
                  keepLits = true;
                  if (ModeledAsBoxType(e.E0.Type)) {
                    e1 = BoxIfNecessary(expr.Origin, e1, e.E1.Type);
                    oe1 = BoxIfNecessary(expr.Origin, oe1, e.E1.Type);
                  } else if (ModeledAsBoxType(e.E1.Type)) {
                    e0 = BoxIfNecessary(expr.Origin, e0, e.E0.Type);
                    oe0 = BoxIfNecessary(expr.Origin, oe0, e.E0.Type);
                  }
                  if (e.E0.Type.IsCoDatatype && e.E1.Type.IsCoDatatype) {
                    var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                    var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                    return BoogieGenerator.CoEqualCall(e.E0.Type.AsCoDatatype, e0args, e1args, null,
                      this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, GetToken(binaryExpr));
                  }
                  if (e.E0.Type.IsIndDatatype && e.E1.Type.IsIndDatatype) {
                    return BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), e.E0.Type, e0, e1);
                  }
                  typ = Boogie.Type.Bool;
                  bOpcode = BinaryOperator.Opcode.Eq;
                  break;
                case BinaryExpr.ResolvedOpcode.NeqCommon:
                  if (ModeledAsBoxType(e.E0.Type)) {
                    e1 = BoxIfNecessary(expr.Origin, e1, e.E1.Type);
                    oe1 = BoxIfNecessary(expr.Origin, oe1, e.E1.Type);
                  } else if (ModeledAsBoxType(e.E1.Type)) {
                    e0 = BoxIfNecessary(expr.Origin, e0, e.E0.Type);
                    oe0 = BoxIfNecessary(expr.Origin, oe0, e.E0.Type);
                  }
                  if (e.E0.Type.IsCoDatatype && e.E1.Type.IsCoDatatype) {
                    var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                    var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                    var eq = BoogieGenerator.CoEqualCall(e.E0.Type.AsCoDatatype, e0args, e1args, null,
                      this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, GetToken(binaryExpr));
                    return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, eq);
                  }
                  if (e.E0.Type.IsIndDatatype && e.E1.Type.IsIndDatatype) {
                    var eq = BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), e.E0.Type, e0, e1);
                    return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, eq);
                  }
                  typ = Boogie.Type.Bool;
                  bOpcode = BinaryOperator.Opcode.Neq;
                  break;
                case BinaryExpr.ResolvedOpcode.Lt:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "lt_bv" + bvWidth, Boogie.Type.Bool, e0, e1, liftLit);
                  } else if (e0Type.IsBigOrdinalType) {
                    return FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e0, e1);
                  } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
                    typ = Boogie.Type.Bool;
                    bOpcode = BinaryOperator.Opcode.Lt;
                    break;
                  } else {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_lt_boogie", Boogie.Type.Bool, e0, e1, liftLit);
                  }
                case BinaryExpr.ResolvedOpcode.LessThanLimit:
                  return FunctionCall(GetToken(binaryExpr), "ORD#LessThanLimit", Boogie.Type.Bool, e0, e1);
                case BinaryExpr.ResolvedOpcode.Le:
                  keepLits = true;
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "le_bv" + bvWidth, Boogie.Type.Bool, e0, e1, false);
                  } else if (e0Type.IsBigOrdinalType) {
                    var less = FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e0, e1);
                    var eq = Boogie.Expr.Eq(e0, e1);
                    return BplOr(eq, less);
                  } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
                    typ = Boogie.Type.Bool;
                    bOpcode = BinaryOperator.Opcode.Le;
                    break;
                  } else {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_le_boogie", Boogie.Type.Bool, e0, e1, false);
                  }
                case BinaryExpr.ResolvedOpcode.Ge:
                  keepLits = true;
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "ge_bv" + bvWidth, Boogie.Type.Bool, e0, e1, false);
                  } else if (e0Type.IsBigOrdinalType) {
                    var less = FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e1, e0);
                    var eq = Boogie.Expr.Eq(e1, e0);
                    return BplOr(eq, less);
                  } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
                    typ = Boogie.Type.Bool;
                    bOpcode = BinaryOperator.Opcode.Ge;
                    break;
                  } else {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_ge_boogie", Boogie.Type.Bool, e0, e1, false);
                  }
                case BinaryExpr.ResolvedOpcode.Gt:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "gt_bv" + bvWidth, Boogie.Type.Bool, e0, e1, liftLit);
                  } else if (e0Type.IsBigOrdinalType) {
                    return FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e1, e0);
                  } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
                    typ = Boogie.Type.Bool;
                    bOpcode = BinaryOperator.Opcode.Gt;
                    break;
                  } else {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_gt_boogie", Boogie.Type.Bool, e0, e1, liftLit);
                  }

                case BinaryExpr.ResolvedOpcode.Add:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "add_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  } else if (e0Type.IsBigOrdinalType) {
                    return TrToFunctionCall(GetToken(binaryExpr), "ORD#Plus", Predef.BigOrdinalType, e0, e1, liftLit);
                  } else if (e0Type.IsCharType) {
                    return TrToFunctionCall(GetToken(binaryExpr), "char#Plus", Predef.CharType, e0, e1, liftLit);
                  } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic) {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_add_boogie", Boogie.Type.Int, e0, e1, liftLit);
                  } else if (!isReal && (options.ArithMode == 2 || 5 <= options.ArithMode)) {
                    return TrToFunctionCall(GetToken(binaryExpr), "Add", Boogie.Type.Int, oe0, oe1, liftLit);
                  } else {
                    typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                    bOpcode = BinaryOperator.Opcode.Add;
                    break;
                  }
                case BinaryExpr.ResolvedOpcode.Sub:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "sub_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  } else if (e0Type.IsBigOrdinalType) {
                    return TrToFunctionCall(GetToken(binaryExpr), "ORD#Minus", Predef.BigOrdinalType, e0, e1, liftLit);
                  } else if (e0Type.IsCharType) {
                    return TrToFunctionCall(GetToken(binaryExpr), "char#Minus", Predef.CharType, e0, e1, liftLit);
                  } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic) {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_sub_boogie", Boogie.Type.Int, e0, e1, liftLit);
                  } else if (!isReal && (options.ArithMode == 2 || 5 <= options.ArithMode)) {
                    return TrToFunctionCall(GetToken(binaryExpr), "Sub", Boogie.Type.Int, oe0, oe1, liftLit);
                  } else {
                    typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                    bOpcode = BinaryOperator.Opcode.Sub;
                    break;
                  }
                case BinaryExpr.ResolvedOpcode.Mul:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "mul_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic) {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_mul_boogie", Boogie.Type.Int, e0, e1, liftLit);
                  } else if (!isReal && options.ArithMode != 0 && options.ArithMode != 3) {
                    return TrToFunctionCall(GetToken(binaryExpr), "Mul", Boogie.Type.Int, oe0, oe1, liftLit);
                  } else {
                    typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                    bOpcode = BinaryOperator.Opcode.Mul;
                    break;
                  }
                case BinaryExpr.ResolvedOpcode.Div:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "div_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic && !isReal) {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_div_boogie", Boogie.Type.Int, e0, e1, liftLit);
                  } else if (!isReal && options.ArithMode != 0 && options.ArithMode != 3) {
                    return TrToFunctionCall(GetToken(binaryExpr), "Div", Boogie.Type.Int, e0, oe1, liftLit);
                  } else if (isReal) {
                    typ = Boogie.Type.Real;
                    bOpcode = BinaryOperator.Opcode.RealDiv;
                    break;
                  } else {
                    typ = Boogie.Type.Int;
                    bOpcode = BinaryOperator.Opcode.Div;
                    break;
                  }
                case BinaryExpr.ResolvedOpcode.Mod:
                  if (0 <= bvWidth) {
                    return TrToFunctionCall(GetToken(binaryExpr), "mod_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  } else if (BoogieGenerator.DisableNonLinearArithmetic && !isReal) {
                    return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_mod_boogie", Boogie.Type.Int, e0, e1, liftLit);
                  } else if (!isReal && options.ArithMode != 0 && options.ArithMode != 3) {
                    return TrToFunctionCall(GetToken(binaryExpr), "Mod", Boogie.Type.Int, e0, oe1, liftLit);
                  } else {
                    typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                    bOpcode = BinaryOperator.Opcode.Mod;
                    break;
                  }

                case BinaryExpr.ResolvedOpcode.LeftShift: {
                    Contract.Assert(0 <= bvWidth);
                    return TrToFunctionCall(GetToken(binaryExpr), "LeftShift_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, BoogieGenerator.ConvertExpression(GetToken(binaryExpr), e1, e.E1.Type, e.Type), liftLit);
                  }
                case BinaryExpr.ResolvedOpcode.RightShift: {
                    Contract.Assert(0 <= bvWidth);
                    return TrToFunctionCall(GetToken(binaryExpr), "RightShift_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, BoogieGenerator.ConvertExpression(GetToken(binaryExpr), e1, e.E1.Type, e.Type), liftLit);
                  }
                case BinaryExpr.ResolvedOpcode.BitwiseAnd: {
                    Contract.Assert(0 <= bvWidth);
                    return TrToFunctionCall(GetToken(binaryExpr), "and_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  }
                case BinaryExpr.ResolvedOpcode.BitwiseOr: {
                    Contract.Assert(0 <= bvWidth);
                    return TrToFunctionCall(GetToken(binaryExpr), "or_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  }
                case BinaryExpr.ResolvedOpcode.BitwiseXor: {
                    Contract.Assert(0 <= bvWidth);
                    return TrToFunctionCall(GetToken(binaryExpr), "xor_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
                  }

                case BinaryExpr.ResolvedOpcode.LtChar:
                case BinaryExpr.ResolvedOpcode.LeChar:
                case BinaryExpr.ResolvedOpcode.GeChar:
                case BinaryExpr.ResolvedOpcode.GtChar: {
                    // work off the original operands (that is, allow them to be lit-wrapped)
                    var operand0 = BoogieGenerator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe0);
                    var operand1 = BoogieGenerator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe1);
                    BinaryOperator.Opcode bOp;
                    switch (e.ResolvedOp) {
                      case BinaryExpr.ResolvedOpcode.LtChar: bOp = BinaryOperator.Opcode.Lt; break;
                      case BinaryExpr.ResolvedOpcode.LeChar: bOp = BinaryOperator.Opcode.Le; break;
                      case BinaryExpr.ResolvedOpcode.GeChar: bOp = BinaryOperator.Opcode.Ge; break;
                      case BinaryExpr.ResolvedOpcode.GtChar: bOp = BinaryOperator.Opcode.Gt; break;
                      default:
                        Contract.Assert(false);  // unexpected case
                        throw new cce.UnreachableException();  // to please compiler
                    }
                    return Boogie.Expr.Binary(GetToken(binaryExpr), bOp, operand0, operand1);
                  }

                case BinaryExpr.ResolvedOpcode.SetEq:
                case BinaryExpr.ResolvedOpcode.MultiSetEq:
                case BinaryExpr.ResolvedOpcode.SeqEq:
                case BinaryExpr.ResolvedOpcode.MapEq:
                  return BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), e.E0.Type, e0, e1);
                case BinaryExpr.ResolvedOpcode.SetNeq:
                case BinaryExpr.ResolvedOpcode.MultiSetNeq:
                case BinaryExpr.ResolvedOpcode.SeqNeq:
                case BinaryExpr.ResolvedOpcode.MapNeq:
                  return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), e.E0.Type, e0, e1));

                case BinaryExpr.ResolvedOpcode.ProperSubset: {
                    return BoogieGenerator.ProperSubset(GetToken(binaryExpr), e0, e1, e.E0.Type.NormalizeToAncestorType().AsSetType.Finite);
                  }
                case BinaryExpr.ResolvedOpcode.Subset: {
                    bool finite = e.E1.Type.NormalizeToAncestorType().AsSetType.Finite;
                    var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
                    return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, null, e0, e1);
                  }
                case BinaryExpr.ResolvedOpcode.Superset: {
                    bool finite = e.E1.Type.NormalizeToAncestorType().AsSetType.Finite;
                    var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
                    return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, null, e1, e0);
                  }
                case BinaryExpr.ResolvedOpcode.ProperSuperset:
                  return BoogieGenerator.ProperSubset(GetToken(binaryExpr), e1, e0, e.E0.Type.NormalizeToAncestorType().AsSetType.Finite);
                case BinaryExpr.ResolvedOpcode.Disjoint: {
                    bool finite = e.E1.Type.NormalizeToAncestorType().AsSetType.Finite;
                    var f = finite ? BuiltinFunction.SetDisjoint : BuiltinFunction.ISetDisjoint;
                    return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, null, e0, e1);
                  }
                case BinaryExpr.ResolvedOpcode.InSet:
                  Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
                case BinaryExpr.ResolvedOpcode.NotInSet:
                  Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
                case BinaryExpr.ResolvedOpcode.Union: {
                    var setType = binaryExpr.Type.NormalizeToAncestorType().AsSetType;
                    bool finite = setType.Finite;
                    var f = finite ? BuiltinFunction.SetUnion : BuiltinFunction.ISetUnion;
                    return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(setType.Arg), e0, e1);
                  }
                case BinaryExpr.ResolvedOpcode.Intersection: {
                    var setType = binaryExpr.Type.NormalizeToAncestorType().AsSetType;
                    bool finite = setType.Finite;
                    var f = finite ? BuiltinFunction.SetIntersection : BuiltinFunction.ISetIntersection;
                    return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(setType.Arg), e0, e1);
                  }
                case BinaryExpr.ResolvedOpcode.SetDifference: {
                    var setType = binaryExpr.Type.NormalizeToAncestorType().AsSetType;
                    bool finite = setType.Finite;
                    var f = finite ? BuiltinFunction.SetDifference : BuiltinFunction.ISetDifference;
                    return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(setType.Arg), e0, e1);
                  }
                case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
                  return BoogieGenerator.ProperMultiset(GetToken(binaryExpr), e0, e1);
                case BinaryExpr.ResolvedOpcode.MultiSubset:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetSubset, null, e0, e1);
                case BinaryExpr.ResolvedOpcode.MultiSuperset:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetSubset, null, e1, e0);
                case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
                  return BoogieGenerator.ProperMultiset(GetToken(binaryExpr), e1, e0);
                case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetDisjoint, null, e0, e1);
                case BinaryExpr.ResolvedOpcode.InMultiSet:
                  Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
                case BinaryExpr.ResolvedOpcode.NotInMultiSet:
                  Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
                case BinaryExpr.ResolvedOpcode.MultiSetUnion:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetUnion,
                    BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsMultiSetType.Arg), e0, e1);
                case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetIntersection,
                    BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsMultiSetType.Arg), e0, e1);
                case BinaryExpr.ResolvedOpcode.MultiSetDifference:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetDifference,
                    BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsMultiSetType.Arg), e0, e1);

                case BinaryExpr.ResolvedOpcode.ProperPrefix:
                  return BoogieGenerator.ProperPrefix(GetToken(binaryExpr), e0, e1);
                case BinaryExpr.ResolvedOpcode.Prefix: {
                    Boogie.Expr len0 = BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqLength, null, e0);
                    Boogie.Expr len1 = BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqLength, null, e1);
                    return Boogie.Expr.Binary(GetToken(binaryExpr), BinaryOperator.Opcode.And,
                      Boogie.Expr.Le(len0, len1),
                      BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
                  }
                case BinaryExpr.ResolvedOpcode.Concat:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqAppend,
                    BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsSeqType.Arg), e0, e1);
                case BinaryExpr.ResolvedOpcode.InSeq:
                  return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqContains, null, e1,
                    BoxIfNecessary(GetToken(binaryExpr), e0, e.E0.Type));
                case BinaryExpr.ResolvedOpcode.NotInSeq:
                  Boogie.Expr arg = BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqContains, null, e1,
                    BoxIfNecessary(GetToken(binaryExpr), e0, e.E0.Type));
                  return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, arg);
                case BinaryExpr.ResolvedOpcode.InMap: {
                    bool finite = e.E1.Type.NormalizeToAncestorType().AsMapType.Finite;
                    var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
                    return BoogieGenerator.IsSetMember(GetToken(binaryExpr),
                      BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, finite ? Predef.MapType : Predef.IMapType, e1),
                      BoxIfNecessary(GetToken(binaryExpr), e0, e.E0.Type),
                      finite);
                  }
                case BinaryExpr.ResolvedOpcode.NotInMap: {
                    bool finite = e.E1.Type.NormalizeToAncestorType().AsMapType.Finite;
                    var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
                    Boogie.Expr inMap = BoogieGenerator.IsSetMember(GetToken(binaryExpr),
                      BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, finite ? Predef.MapType : Predef.IMapType, e1),
                      BoxIfNecessary(GetToken(binaryExpr), e0, e.E0.Type),
                      finite);
                    return Boogie.Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, inMap);
                  }
                case BinaryExpr.ResolvedOpcode.MapMerge: {
                    bool finite = e0Type.NormalizeToAncestorType().AsMapType.Finite;
                    var f = finite ? "Map#Merge" : "IMap#Merge";
                    return FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(binaryExpr.Type), e0, e1);
                  }
                case BinaryExpr.ResolvedOpcode.MapSubtraction: {
                    bool finite = e0Type.NormalizeToAncestorType().AsMapType.Finite;
                    var f = finite ? "Map#Subtract" : "IMap#Subtract";
                    return FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(binaryExpr.Type), e0, e1);
                  }

                case BinaryExpr.ResolvedOpcode.RankLt:
                  return Boogie.Expr.Binary(GetToken(binaryExpr), BinaryOperator.Opcode.Lt,
                    BoogieGenerator.FunctionCall(GetToken(binaryExpr), e0Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e0),
                    BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.DtRank, null, e1));
                case BinaryExpr.ResolvedOpcode.RankGt:
                  return Boogie.Expr.Binary(GetToken(binaryExpr), BinaryOperator.Opcode.Gt,
                    BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.DtRank, null, e0),
                    BoogieGenerator.FunctionCall(GetToken(binaryExpr), e.E1.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e1));

                default:
                  Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
              }
              liftLit = liftLit && !keepLits;
              var ae0 = keepLits ? oe0 : e0;
              var ae1 = keepLits ? oe1 : e1;
              Boogie.Expr re = Boogie.Expr.Binary(GetToken(binaryExpr), bOpcode, ae0, ae1);
              if (liftLit) {
                re = MaybeLit(re, typ);
              }
              return re;
            }
          case TernaryExpr ternaryExpr: {
              var e = ternaryExpr;
              var e0 = TrExpr(e.E0);
              if (!e.E0.Type.IsBigOrdinalType) {
                e0 = FunctionCall(e0.tok, "ORD#FromNat", Predef.BigOrdinalType, e0);
              }
              var e1 = TrExpr(e.E1);
              var e2 = TrExpr(e.E2);
              switch (e.Op) {
                case TernaryExpr.Opcode.PrefixEqOp:
                case TernaryExpr.Opcode.PrefixNeqOp:
                  var e1type = e.E1.Type.NormalizeExpand();
                  var e2type = e.E2.Type.NormalizeExpand();
                  var cot = e1type.AsCoDatatype;
                  Contract.Assert(cot != null);  // the argument types of prefix equality (and prefix disequality) are codatatypes
                  var r = BoogieGenerator.CoEqualCall(cot, e1type.TypeArgs, e2type.TypeArgs, e0, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e1, e2);
                  if (e.Op == TernaryExpr.Opcode.PrefixEqOp) {
                    return r;
                  } else {
                    return Boogie.Expr.Unary(GetToken(ternaryExpr), UnaryOperator.Opcode.Not, r);
                  }
                default:
                  Contract.Assert(false); throw new cce.UnreachableException();  // unexpected ternary expression
              }
            }
          case LetExpr letExpr:
            return TrLetExpr(letExpr);
          case QuantifierExpr quantifierExpr: {
              QuantifierExpr e = quantifierExpr;

              if (e.SplitQuantifier != null) {
                return TrExpr(e.SplitQuantifierExpression);
              } else {
                List<Variable> bvars = [];
                var bodyEtran = this;
                if (e is ExistsExpr && BoogieGenerator.stmtContext == StmtType.ASSERT && BoogieGenerator.adjustFuelForExists) {
                  // assert exists need decrease fuel by 1
                  bodyEtran = bodyEtran.DecreaseFuel(1);
                  // set adjustFuelForExists to false so that we don't keep decrease the fuel in cases like the expr below.
                  // assert exists p:int :: exists t:T :: ToInt(t) > 0;
                  BoogieGenerator.adjustFuelForExists = false;
                } else if (e is ExistsExpr && BoogieGenerator.stmtContext == StmtType.ASSUME && BoogieGenerator.adjustFuelForExists) {
                  // assume exists need increase fuel by 1
                  bodyEtran = bodyEtran.LayerOffset(1);
                  BoogieGenerator.adjustFuelForExists = false;
                }

                Boogie.Expr antecedent = Boogie.Expr.True;

                List<bool> freeOfAlloc = BoundedPool.HasBounds(e.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
                antecedent = BplAnd(antecedent, bodyEtran.TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc)); // initHeapForAllStmt

                Boogie.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
                Boogie.Trigger tr = BoogieGenerator.TrTrigger(bodyEtran, e.Attributes, GetToken(e), bvars, null, null);

                if (e.Range != null) {
                  antecedent = BplAnd(antecedent, bodyEtran.TrExpr(e.Range));
                }
                Boogie.Expr body = bodyEtran.TrExpr(e.Term);

                if (e is ForallExpr) {
                  return new Boogie.ForallExpr(GetToken(quantifierExpr), [], bvars, kv, tr, BplImp(antecedent, body));
                } else {
                  Contract.Assert(e is ExistsExpr);
                  return new Boogie.ExistsExpr(GetToken(quantifierExpr), [], bvars, kv, tr, BplAnd(antecedent, body));
                }
              }
            }
          case SetComprehension comprehension: {
              var e = comprehension;
              List<bool> freeOfAlloc = BoundedPool.HasBounds(e.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);

              // Translate "set xs | R :: T" into:
              //     Set#FromBoogieMap(lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T)))
              // or if "T" is "xs", then:
              //     Set#FromBoogieMap(lambda y: BoxType :: CorrectType(y) && R[xs := Unbox(y)])
              // where Set#FromBoogieMap is omitted for iset.
              // FIXME: This is not a good translation, see comment in PreludeCore.bpl. It should be changed to not use a Boogie lambda expression
              // but to instead do the lambda lifting here.
              var yVar = new Boogie.BoundVariable(GetToken(comprehension), new Boogie.TypedIdent(GetToken(comprehension), BoogieGenerator.CurrentIdGenerator.FreshId("$y#"), Predef.BoxType));
              Boogie.Expr y = new Boogie.IdentifierExpr(GetToken(comprehension), yVar);
              Boogie.Expr lbody;
              if (e.TermIsSimple) {
                var bv = e.BoundVars[0];
                // lambda y: BoxType :: CorrectType(y) && R[xs := yUnboxed]
                Boogie.Expr typeAntecedent = BoogieGenerator.MkIsBox(new Boogie.IdentifierExpr(GetToken(comprehension), yVar), bv.Type);
                if (freeOfAlloc != null && !freeOfAlloc[0]) {
                  var isAlloc = BoogieGenerator.MkIsAllocBox(new Boogie.IdentifierExpr(GetToken(comprehension), yVar), bv.Type, HeapExpr);
                  typeAntecedent = BplAnd(typeAntecedent, isAlloc);
                }
                var yUnboxed = BoogieGenerator.UnboxUnlessInherentlyBoxed(new Boogie.IdentifierExpr(GetToken(comprehension), yVar), bv.Type);
                var range = BoogieGenerator.Substitute(e.Range, bv, new BoogieWrapper(yUnboxed, bv.Type));
                lbody = BplAnd(typeAntecedent, TrExpr(range));
              } else {
                // lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))
                List<Variable> bvars = [];
                Boogie.Expr typeAntecedent = TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc);

                var eq = Boogie.Expr.Eq(y, BoxIfNecessary(GetToken(comprehension), TrExpr(e.Term), e.Term.Type));
                var ebody = BplAnd(BplAnd(typeAntecedent, TrExpr(e.Range)), eq);
                var triggers = BoogieGenerator.TrTrigger(this, e.Attributes, GetToken(e));
                lbody = new Boogie.ExistsExpr(GetToken(comprehension), bvars, triggers, ebody);
              }
              Boogie.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
              var lambda = new Boogie.LambdaExpr(GetToken(comprehension), [], [yVar], kv, lbody);
              return comprehension.Type.NormalizeToAncestorType().AsSetType.Finite
                ? FunctionCall(GetToken(comprehension), "Set#FromBoogieMap", Predef.SetType, lambda)
                : lambda;
            }
          case MapComprehension comprehension: {
              var e = comprehension;
              // Translate "map x,y | R(x,y) :: F(x,y) := G(x,y)" into
              // Map#Glue(lambda w: BoxType :: exists x,y :: R(x,y) && unbox(w) == F(x,y),
              //          lambda w: BoxType :: G(project_x(unbox(w)), project_y(unbox(w))),
              //          type)".
              // where project_x and project_y are functions defined (elsewhere, in CanCallAssumption) by the following axiom:
              //     forall x,y :: R(x,y) ==> var x',y' := project_x(unbox(F(x,y))),project_y(unbox(F(x,y))); R(x',y') && F(x',y') == F(x,y)
              // that is (without the let expression):
              //     forall x,y :: R(x,y) ==> R(project_x(unbox(F(x,y))), project_y(unbox(F(x,y)))) && F(project_x(unbox(F(x,y))), project_y(unbox(F(x,y)))) == F(x,y)
              //
              // In the common case where F(x,y) is omitted (in which case the list of bound variables is restricted to length 1):
              // Translate "map x | R(x) :: G(x)" into
              // Map#Glue(lambda w: BoxType :: R(unbox(w)),
              //          lambda w: BoxType :: G(unbox(w)),
              //          type)".
              List<Variable> bvars = [];
              List<bool> freeOfAlloc = BoundedPool.HasBounds(e.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);

              Boogie.QKeyValue kv = TrAttributes(e.Attributes, "trigger");

              var wVar = new Boogie.BoundVariable(GetToken(comprehension), new Boogie.TypedIdent(GetToken(comprehension), BoogieGenerator.CurrentIdGenerator.FreshId("$w#"), Predef.BoxType));

              Boogie.Expr keys, values;
              if (!e.IsGeneralMapComprehension) {
                var bv = e.BoundVars[0];
                var w = new Boogie.IdentifierExpr(GetToken(comprehension), wVar);
                Boogie.Expr unboxw = BoogieGenerator.UnboxUnlessInherentlyBoxed(w, bv.Type);
                Boogie.Expr typeAntecedent = BoogieGenerator.MkIsBox(w, bv.Type);
                if (freeOfAlloc != null && !freeOfAlloc[0]) {
                  var isAlloc = BoogieGenerator.MkIsAllocBox(w, bv.Type, HeapExpr);
                  typeAntecedent = BplAnd(typeAntecedent, isAlloc);
                }
                var subst = new Dictionary<IVariable, Expression>();
                subst.Add(bv, new BoogieWrapper(unboxw, bv.Type));

                var ebody = BplAnd(typeAntecedent, TrExpr(BoogieGenerator.Substitute(e.Range, null, subst)));
                keys = new Boogie.LambdaExpr(GetToken(e), [], [wVar], kv, ebody);
                ebody = TrExpr(BoogieGenerator.Substitute(e.Term, null, subst));
                values = new Boogie.LambdaExpr(GetToken(e), [], [wVar], kv, BoxIfNecessary(GetToken(comprehension), ebody, e.Term.Type));
              } else {
                var t = e.TermLeft;
                var w = new Boogie.IdentifierExpr(GetToken(comprehension), wVar);
                Boogie.Expr unboxw = BoogieGenerator.UnboxUnlessInherentlyBoxed(w, t.Type);
                Boogie.Expr typeAntecedent = BoogieGenerator.MkIsBox(w, t.Type);
                if (freeOfAlloc != null && !freeOfAlloc[0]) {
                  var isAlloc = BoogieGenerator.MkIsAllocBox(w, t.Type, HeapExpr);
                  typeAntecedent = BplAnd(typeAntecedent, isAlloc);
                }

                BoogieGenerator.CreateBoundVariables(e.BoundVars, out var bvs, out var args);
                Contract.Assert(e.BoundVars.Count == bvs.Count);
                var subst = new Dictionary<IVariable, Expression>();
                for (var i = 0; i < e.BoundVars.Count; i++) {
                  subst.Add(e.BoundVars[i], new BoogieWrapper(args[i], e.BoundVars[i].Type));
                }
                var rr = TrExpr(BoogieGenerator.Substitute(e.Range, null, subst));
                var ff = TrExpr(BoogieGenerator.Substitute(t, null, subst));
                var exst_body = BplAnd(rr, Boogie.Expr.Eq(unboxw, ff));
                var ebody = BplAnd(typeAntecedent, new Boogie.ExistsExpr(GetToken(e), bvs, exst_body));
                keys = new Boogie.LambdaExpr(GetToken(e), [], [wVar], kv, ebody);

                BoogieGenerator.CreateMapComprehensionProjectionFunctions(e);
                Contract.Assert(e.ProjectionFunctions != null && e.ProjectionFunctions.Count == e.BoundVars.Count);
                subst = new Dictionary<IVariable, Expression>();
                for (var i = 0; i < e.BoundVars.Count; i++) {
                  var p = new Boogie.NAryExpr(GetToken(e), new Boogie.FunctionCall(e.ProjectionFunctions[i]), new List<Boogie.Expr> { unboxw });
                  var prj = new BoogieWrapper(p, e.BoundVars[i].Type);
                  subst.Add(e.BoundVars[i], prj);
                }
                ebody = TrExpr(BoogieGenerator.Substitute(e.Term, null, subst));
                values = new Boogie.LambdaExpr(GetToken(e), [], [wVar], kv, BoxIfNecessary(GetToken(comprehension), ebody, e.Term.Type));
              }

              return BoogieGenerator.FunctionCall(GetToken(e),
                e.Finite ? BuiltinFunction.MapGlue : BuiltinFunction.IMapGlue,
                null,
                e.Finite ? FunctionCall(GetToken(comprehension), "Set#FromBoogieMap", Predef.SetType, keys) : keys,
                values, BoogieGenerator.TypeToTy(comprehension.Type));
            }
          case LambdaExpr lambdaExpr: {
              var e = lambdaExpr;
              return TrLambdaExpr(e);
            }
          case StmtExpr stmtExpr: {
              var e = stmtExpr;
              return TrExpr(e.E);
            }
          case ITEExpr iteExpr: {
              ITEExpr e = iteExpr;
              var g = BoogieGenerator.RemoveLit(TrExpr(e.Test));
              var thn = BoogieGenerator.AdaptBoxing(e.Thn.Origin, BoogieGenerator.RemoveLit(TrExpr(e.Thn)), e.Thn.Type, e.Type);
              var els = BoogieGenerator.AdaptBoxing(e.Els.Origin, BoogieGenerator.RemoveLit(TrExpr(e.Els)), e.Els.Type, e.Type);
              return new NAryExpr(GetToken(iteExpr), new IfThenElse(GetToken(iteExpr)), new List<Boogie.Expr> { g, thn, els });
            }
          case MatchExpr matchExpr: {
              var e = matchExpr;
              var ite = DesugarMatchExpr(e);
              return TrExpr(ite);
            }
          case ConcreteSyntaxExpression expression: {
              var e = expression;
              return TrExpr(e.ResolvedExpression);
            }
          case NestedMatchExpr nestedMatchExpr:
            return TrExpr(nestedMatchExpr.Flattened);
          case BoxingCastExpr castExpr: {
              BoxingCastExpr e = castExpr;
              return BoogieGenerator.CondApplyBox(GetToken(e), TrExpr(e.E), e.FromType, e.ToType);
            }
          case UnboxingCastExpr castExpr: {
              UnboxingCastExpr e = castExpr;
              return BoogieGenerator.CondApplyUnbox(GetToken(e), TrExpr(e.E), e.FromType, e.ToType);
            }
          case DecreasesToExpr decreasesToExpr:
            var oldArray = decreasesToExpr.OldExpressions.ToArray();
            var newArray = decreasesToExpr.NewExpressions.ToArray();
            List<Expr> newExprs = [];
            List<Expr> oldExprs = [];
            List<Expression> newExprsDafny = [];
            List<Expression> oldExprsDafny = [];
            int N = Math.Min(oldArray.Length, newArray.Length);
            for (int i = 0; i < N; i++) {
              if (!CompatibleDecreasesTypes(oldArray[i].Type, newArray[i].Type)) {
                N = i;
                break;
              }
              oldExprsDafny.Add(oldArray[i]);
              oldExprs.Add(TrExpr(oldArray[i]));
              newExprsDafny.Add(newArray[i]);
              newExprs.Add(TrExpr(newArray[i]));
            }

            bool endsWithWinningTopComparison = N == oldArray.Length && N < newArray.Length;
            var allowNoChange = decreasesToExpr.AllowNoChange || endsWithWinningTopComparison;
            List<IOrigin> toks = oldExprs.Zip(newExprs, (_, _) => (IOrigin)decreasesToExpr.Origin).ToList();
            var decreasesExpr = BoogieGenerator.DecreasesCheck(toks, null,
              newExprsDafny, oldExprsDafny, newExprs, oldExprs, null,
              null, allowNoChange, false);
            return decreasesExpr;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
        }
      }

      public Expr TrExprSpecialFunctionCall(FunctionCallExpr expr) {
        Contract.Requires(expr.Function is SpecialFunction);
        string name = expr.Function.Name;
        if (name == "RotateLeft") {
          var w = expr.Type.AsBitVectorType.Width;
          Expression arg = expr.Args[0];
          return TrToFunctionCall(GetToken(expr), "LeftRotate_bv" + w, BoogieGenerator.BplBvType(w), TrExpr(expr.Receiver), BoogieGenerator.ConvertExpression(GetToken(expr), TrExpr(arg), arg.Type, expr.Type), false);
        } else if (name == "RotateRight") {
          var w = expr.Type.AsBitVectorType.Width;
          Expression arg = expr.Args[0];
          return TrToFunctionCall(GetToken(expr), "RightRotate_bv" + w, BoogieGenerator.BplBvType(w), TrExpr(expr.Receiver), BoogieGenerator.ConvertExpression(GetToken(expr), TrExpr(arg), arg.Type, expr.Type), false);
        } else {
          bool argsAreLitDummy;
          var args = FunctionInvocationArguments(expr, null, null, true, out argsAreLitDummy);
          var id = new Boogie.IdentifierExpr(GetToken(expr), expr.Function.FullSanitizedName, BoogieGenerator.TrType(expr.Type));
          return new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(id), args);
        }
      }
      public Expr TrToFunctionCall(Boogie.IToken tok, string function, Boogie.Type returnType, Boogie.Expr e0, Boogie.Expr e1, bool liftLit) {
        Boogie.Expr re = FunctionCall(tok, function, returnType, e0, e1);
        if (liftLit) {
          re = MaybeLit(re, returnType);
        }
        return re;
      }

      private Expr TrLambdaExpr(LambdaExpr e) {
        Contract.Requires(e != null);

        var bvars = new List<Boogie.Variable>();

        var varNameGen = BoogieGenerator.CurrentIdGenerator.NestedFreshIdGenerator("$l#");

        var heap = BplBoundVar(varNameGen.FreshId("#heap#"), Predef.HeapType, bvars);

        var ves = (from bv in e.BoundVars
                   select
BplBoundVar(varNameGen.FreshId(string.Format("#{0}#", bv.Name)), Predef.BoxType, bvars)).ToList();
        var subst = e.BoundVars.Zip(ves, (bv, ve) => {
          var unboxy = BoogieGenerator.UnboxUnlessInherentlyBoxed(ve, bv.Type);
          return new KeyValuePair<IVariable, Expression>(bv, new BoogieWrapper(unboxy, bv.Type));
        }).ToDictionary(x => x.Key, x => x.Value);
        var su = new Substituter(null, subst, new Dictionary<TypeParameter, Type>());
        var et = this.HeapExpr != null
          ? new ExpressionTranslator(this.BoogieGenerator, this.Predef, heap, this.Old.HeapExpr, this.scope)
          : new ExpressionTranslator(this, heap);
        var lvars = new List<Boogie.Variable>();
        var ly = BplBoundVar(varNameGen.FreshId("#ly#"), Predef.LayerType, lvars);
        et = et.WithLayer(ly);

        var ebody = et.TrExpr(BoogieGenerator.Substitute(e.Body, null, subst));
        ebody = BoogieGenerator.BoxIfNotNormallyBoxed(ebody.tok, ebody, e.Body.Type);

        var isBoxes = BplAnd(ves.Zip(e.BoundVars, (ve, bv) => BoogieGenerator.MkIsBox(ve, bv.Type)));
        Bpl.Expr reqbody;
        if (e.Range == null) {
          reqbody = isBoxes;
        } else {
          var range = BoogieGenerator.Substitute(e.Range, null, subst);
          reqbody = BplAnd(isBoxes, BplImp(et.CanCallAssumption(range), et.TrExpr(range)));
        }

        var rdvars = new List<Boogie.Variable>();
        var o = BplBoundVar(varNameGen.FreshId("#o#"), Predef.RefType, rdvars);
        Boogie.Expr rdbody = new Boogie.LambdaExpr(GetToken(e), [], rdvars, null,
          BoogieGenerator.InRWClause(GetToken(e), o, null, e.Reads.Expressions.ConvertAll(su.SubstFrameExpr), et, null, null));
        rdbody = FunctionCall(GetToken(e), "SetRef_to_SetBox", Predef.SetType, rdbody);

        return MaybeLit(
          BoogieGenerator.FunctionCall(GetToken(e), BuiltinFunction.AtLayer, Predef.HandleType,
            new Boogie.LambdaExpr(GetToken(e), [], lvars, null,
              FunctionCall(GetToken(e), BoogieGenerator.Handle(e.BoundVars.Count), Predef.BoxType,
                new Boogie.LambdaExpr(GetToken(e), [], bvars, null, ebody),
                new Boogie.LambdaExpr(GetToken(e), [], bvars, null, reqbody),
                new Boogie.LambdaExpr(GetToken(e), [], bvars, null, rdbody))),
            layerIntraCluster != null ? layerIntraCluster.ToExpr() : layerInterCluster.ToExpr()),
          Predef.HandleType);
      }

      public Expression DesugarMatchExpr(MatchExpr e) {
        Contract.Requires(e != null);
        // Translate:
        //   match S
        //   case C(i, j) => X
        //   case D(k, l) => Y
        //   case E(m, n) => Z
        // into:
        //   if S.C? then
        //     X[i,j := S.dC0, S.dC1]
        //   else if S.D? then
        //     Y[k,l := S.dD0, S.dD1]
        //   else
        //     Z[m,n := S.dE0, S.dE1]
        // As a special case, when there are no cases at all (which, in a correct program, means the
        // match expression is unreachable), the translation is:
        //   t
        // where is "t" is some value (in particular, the default value) of the expected type.
        Expression r = null;
        for (int i = e.Cases.Count; 0 <= --i;) {
          var mc = e.Cases[i];
          var substMap = new Dictionary<IVariable, Expression>();
          var argIndex = 0;
          foreach (var bv in mc.Arguments) {
            if (!LocalVariable.HasWildcardName(bv)) {
              var dtor = mc.Ctor.Destructors[argIndex];
              var dv = new MemberSelectExpr(bv.Origin, e.Source, dtor);
              substMap.Add(bv, dv);
            }
            argIndex++;
          }
          var c = BoogieGenerator.Substitute(mc.Body, null, substMap);
          if (r == null) {
            r = c;
          } else {
            var test = new MemberSelectExpr(mc.Origin, e.Source, mc.Ctor.QueryField);
            var ite = new ITEExpr(mc.Origin, false, test, c, r);
            ite.Type = e.Type;
            r = ite;
          }
        }
        return r ?? new BoogieWrapper(ArbitraryValue(e.Type), e.Type);
      }

      public Boogie.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, List<Variable> bvars) {
        return TrBoundVariables(boundVars, bvars, false);
      }

      public Boogie.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, List<Variable> bvars, bool translateAsLocals, List<bool>/*?*/ freeOfAlloc = null) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);
        Contract.Requires(freeOfAlloc == null || freeOfAlloc.Count == boundVars.Count);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        Boogie.Expr typeAntecedent = Boogie.Expr.True;
        var i = 0;
        foreach (BoundVar bv in boundVars) {
          var tid = new Boogie.TypedIdent(bv.Origin, bv.AssignUniqueName(BoogieGenerator.CurrentDeclaration.IdGenerator), BoogieGenerator.TrType(bv.Type));
          Boogie.Variable bvar;
          if (translateAsLocals) {
            bvar = new Boogie.LocalVariable(bv.Origin, tid);
          } else {
            bvar = new Boogie.BoundVariable(bv.Origin, tid);
          }
          bvars.Add(bvar);
          var useAlloc = freeOfAlloc == null || freeOfAlloc[i] ? NOALLOC : ISALLOC;
          Boogie.Expr wh = BoogieGenerator.GetWhereClause(bv.Origin, new Boogie.IdentifierExpr(bv.Origin, bvar), bv.Type, this, useAlloc);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
          i++;
        }
        return typeAntecedent;
      }

      public List<Tuple<Boogie.Variable, Boogie.Expr>> TrBoundVariables_SeparateWhereClauses(List<BoundVar/*!*/> boundVars) {
        Contract.Requires(boundVars != null);
        Contract.Ensures(Contract.Result<List<Tuple<Boogie.Variable, Boogie.Expr>>>() != null);

        var varsAndAntecedents = new List<Tuple<Boogie.Variable, Boogie.Expr>>();
        foreach (BoundVar bv in boundVars) {
          var tid = new Boogie.TypedIdent(bv.Origin, bv.AssignUniqueName(BoogieGenerator.CurrentDeclaration.IdGenerator), BoogieGenerator.TrType(bv.Type));
          var bvar = new Boogie.BoundVariable(bv.Origin, tid);
          var wh = BoogieGenerator.GetWhereClause(bv.Origin, new Boogie.IdentifierExpr(bv.Origin, bvar), bv.Type, this, NOALLOC);
          varsAndAntecedents.Add(Tuple.Create<Boogie.Variable, Boogie.Expr>(bvar, wh));
        }
        return varsAndAntecedents;
      }

      public Boogie.Expr TrBoundVariablesRename(List<BoundVar> boundVars, List<Variable> bvars, out Dictionary<IVariable, Expression> substMap) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);

        substMap = new Dictionary<IVariable, Expression>();
        Boogie.Expr typeAntecedent = Boogie.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var newBoundVar = new BoundVar(bv.Origin, bv.Name, bv.Type);
          IdentifierExpr ie = new IdentifierExpr(newBoundVar.Origin, newBoundVar.AssignUniqueName(BoogieGenerator.CurrentDeclaration.IdGenerator)) {
            Var = newBoundVar,
            Type = newBoundVar.Type
          };
          substMap.Add(bv, ie);
          Boogie.Variable bvar = new Boogie.BoundVariable(newBoundVar.Origin, new Boogie.TypedIdent(newBoundVar.Origin, newBoundVar.AssignUniqueName(BoogieGenerator.CurrentDeclaration.IdGenerator), BoogieGenerator.TrType(newBoundVar.Type)));
          bvars.Add(bvar);
          var bIe = new Boogie.IdentifierExpr(bvar.tok, bvar);
          Boogie.Expr wh = BoogieGenerator.GetWhereClause(bv.Origin, bIe, newBoundVar.Type, this, NOALLOC);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public List<Boogie.Expr> FunctionInvocationArguments(FunctionCallExpr e, Boogie.Expr layerArgument, Boogie.Expr revealArgument) {
        bool dummy;
        return FunctionInvocationArguments(e, layerArgument, revealArgument, false, out dummy);
      }

      public List<Boogie.Expr> FunctionInvocationArguments(FunctionCallExpr e, Boogie.Expr layerArgument, Boogie.Expr revealArgument, bool omitHeapArgument, out bool argsAreLit) {
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<List<Boogie.Expr>>() != null);

        var args = new List<Boogie.Expr>();

        // first add type arguments
        var tyParams = GetTypeParams(e.Function);
        var tySubst = e.TypeArgumentSubstitutionsWithParents();
        args.AddRange(BoogieGenerator.TrTypeArgs(tySubst, tyParams));

        if (layerArgument != null) {
          args.Add(layerArgument);
        }
        if (revealArgument != null) {
          args.Add(revealArgument);
        }
        if (e.Function is TwoStateFunction) {
          args.Add(OldAt(e.AtLabel).HeapExpr);
        }
        if (!omitHeapArgument && e.Function.ReadsHeap) {
          Contract.Assert(HeapExpr != null);
          args.Add(HeapExpr);
          // If the function doesn't use the heap, but global settings say to use it,
          // then we want to quantify over the heap so that heap in the trigger can match over
          // heap modifying operations. (see Test/dafny4/Bug144.dfy)
          bool usesHeap = e.Function.ReadsHeap || e.Function.Ins.Any(f => f.Type.IsRefType);
          if (!usesHeap) {
            Statistics_HeapAsQuantifierCount++;
          }
        }
        argsAreLit = true;
        if (!e.Function.IsStatic) {
          var tr_ee = BoogieGenerator.BoxifyForTraitParent(e.Origin, TrExpr(e.Receiver), e.Function, e.Receiver.Type);
          argsAreLit = argsAreLit && BoogieGenerator.IsLit(tr_ee);
          args.Add(tr_ee);
        }
        for (int i = 0; i < e.Args.Count; i++) {
          Expression ee = e.Args[i];
          Type t = e.Function.Ins[i].Type;
          Expr tr_ee = TrExpr(ee);
          argsAreLit = argsAreLit && BoogieGenerator.IsLit(tr_ee);
          args.Add(BoogieGenerator.AdaptBoxing(GetToken(e), tr_ee, cce.NonNull(ee.Type), t));
        }
        return args;
      }

      public Boogie.Expr GetArrayIndexFieldName(IOrigin tok, List<Expression> indices) {
        return BoogieGenerator.GetArrayIndexFieldName(tok, indices.ConvertAll(idx => {
          var e = TrExpr(idx);
          return BoogieGenerator.ConvertExpression(GetToken(idx), e, idx.Type, Type.Int);
        }));
      }

      public Boogie.Expr BoxIfNecessary(IOrigin tok, Boogie.Expr e, Type fromType) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(fromType != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);
        return BoogieGenerator.BoxIfNecessary(tok, e, fromType);
      }

      /// <summary>
      /// Translate like s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// </summary>
      public Boogie.Expr TrInSet(IOrigin tok, Boogie.Expr elmt, Expression s, Type elmtType, bool isFiniteSet, bool aggressive, out bool performedRewrite) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
        var r = TrInSet_Aux(tok, elmt, elmtBox, s, isFiniteSet, aggressive, out performedRewrite);
        Contract.Assert(performedRewrite == RewriteInExpr(s, aggressive)); // sanity check
        return r;
      }
      /// <summary>
      /// The worker routine for TrInSet.  This method takes both "elmt" and "elmtBox" as parameters,
      /// using the former when the unboxed form is needed and the latter when the boxed form is needed.
      /// This gives the caller the flexibility to pass in either "o, Box(o)" or "Unbox(bx), bx".
      /// Note: This method must be kept in synch with RewriteInExpr.
      /// </summary>
      public Boogie.Expr TrInSet_Aux(IOrigin tok, Boogie.Expr elmt, Boogie.Expr elmtBox, Expression s, bool isFiniteSet, bool aggressive, out bool performedRewrite) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(elmtBox != null);
        Contract.Requires(s != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        performedRewrite = true;  // assume a rewrite will happen
        s = s.Resolved;
        bool pr;
        if (s is BinaryExpr && aggressive) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Union:
              return BplOr(
                TrInSet_Aux(tok, elmt, elmtBox, bin.E0, isFiniteSet, aggressive, out pr),
                TrInSet_Aux(tok, elmt, elmtBox, bin.E1, isFiniteSet, aggressive, out pr));
            case BinaryExpr.ResolvedOpcode.Intersection:
              return BplAnd(
                TrInSet_Aux(tok, elmt, elmtBox, bin.E0, isFiniteSet, aggressive, out pr),
                TrInSet_Aux(tok, elmt, elmtBox, bin.E1, isFiniteSet, aggressive, out pr));
            case BinaryExpr.ResolvedOpcode.SetDifference:
              return BplAnd(
                TrInSet_Aux(tok, elmt, elmtBox, bin.E0, isFiniteSet, aggressive, out pr),
                Boogie.Expr.Not(TrInSet_Aux(tok, elmt, elmtBox, bin.E1, isFiniteSet, aggressive, out pr)));
            default:
              break;
          }
        } else if (s is SetDisplayExpr) {
          SetDisplayExpr disp = (SetDisplayExpr)s;
          Boogie.Expr disjunction = null;
          foreach (Expression a in disp.Elements) {
            Boogie.Expr disjunct = Boogie.Expr.Eq(elmt, TrExpr(a));
            if (disjunction == null) {
              disjunction = disjunct;
            } else {
              disjunction = BplOr(disjunction, disjunct);
            }
          }
          if (disjunction == null) {
            return Boogie.Expr.False;
          } else {
            return disjunction;
          }
        } else if (s is SetComprehension) {
          var compr = (SetComprehension)s;
          // Translate "elmt in set xs | R :: T" into:
          //     exists xs :: CorrectType(xs) && R && elmt==T
          // or if "T" is "xs", then:
          //     CorrectType(elmt) && R[xs := elmt]
          if (compr.TermIsSimple) {
            // CorrectType(elmt) && R[xs := elmt]
            // Note, we can always use NOALLOC here.
            Boogie.Expr typeAntecedent = BoogieGenerator.GetWhereClause(GetToken(compr), elmt, compr.BoundVars[0].Type, this, NOALLOC) ?? Boogie.Expr.True;
            var range = BoogieGenerator.Substitute(compr.Range, compr.BoundVars[0], new BoogieWrapper(elmt, compr.BoundVars[0].Type));
            return BplAnd(typeAntecedent, TrExpr(range));
          } else {
            // exists xs :: CorrectType(xs) && R && elmt==T
            List<bool> freeOfAlloc = BoundedPool.HasBounds(compr.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
            var bvars = new List<Variable>();
            Boogie.Expr typeAntecedent = TrBoundVariables(compr.BoundVars, bvars, false, freeOfAlloc) ?? Boogie.Expr.True;
            var eq = Boogie.Expr.Eq(elmtBox, BoxIfNecessary(GetToken(compr), TrExpr(compr.Term), compr.Term.Type));
            var ebody = BplAnd(BplAnd(typeAntecedent, TrExpr(compr.Range)), eq);
            var triggers = BoogieGenerator.TrTrigger(this, compr.Attributes, GetToken(compr));
            return new Boogie.ExistsExpr(GetToken(compr), bvars, triggers, ebody);
          }
        }
        performedRewrite = false;
        return BoogieGenerator.IsSetMember(tok, TrExpr(s), elmtBox, isFiniteSet);
      }

      /// <summary>
      /// Translate like 0 < s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// Note: This method must be kept in synch with RewriteInExpr.
      /// </summary>
      public Boogie.Expr TrInMultiSet(IOrigin tok, Boogie.Expr elmt, Expression s, Type elmtType, bool aggressive) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);

        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);
        var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
        return TrInMultiSet_Aux(tok, elmt, elmtBox, s, aggressive);
      }
      public Boogie.Expr TrInMultiSet_Aux(IOrigin tok, Boogie.Expr elmt, Boogie.Expr elmtBox, Expression s, bool aggressive) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtBox != null);

        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        s = s.Resolved;
        if (s is BinaryExpr && aggressive) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
              return Boogie.Expr.Binary(tok, BinaryOperator.Opcode.Or, TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive), TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive));
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return Boogie.Expr.Binary(tok, BinaryOperator.Opcode.And, TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive), TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive));
            default:
              break;
          }
        } else if (s is MultiSetDisplayExpr) {
          MultiSetDisplayExpr disp = (MultiSetDisplayExpr)s;
          Boogie.Expr disjunction = null;
          foreach (Expression a in disp.Elements) {
            Boogie.Expr disjunct = Boogie.Expr.Eq(elmt, TrExpr(a));
            if (disjunction == null) {
              disjunction = disjunct;
            } else {
              disjunction = BplOr(disjunction, disjunct);
            }
          }
          if (disjunction == null) {
            return Boogie.Expr.False;
          } else {
            return disjunction;
          }
        }
        var result = Boogie.Expr.Gt(BoogieGenerator.MultisetMultiplicity(tok, TrExpr(s), elmtBox), Boogie.Expr.Literal(0));
        result.tok = tok;
        return result;
      }

      /// <summary>
      /// This method returns "true" iff TrInSet_Aux/TrInMultiSet_Aux will rewrite an expression "x in s".
      /// Note: This method must be kept in synch with TrInSet_Aux/TrInMultiSet_Aux.
      /// </summary>
      public static bool RewriteInExpr(Expression s, bool aggressive) {
        Contract.Requires(s != null);

        s = s.Resolved;
        if (s is BinaryExpr && aggressive) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Union:
            case BinaryExpr.ResolvedOpcode.Intersection:
            case BinaryExpr.ResolvedOpcode.SetDifference:
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return true;
            default:
              break;
          }
        } else if (s is SetDisplayExpr || s is MultiSetDisplayExpr) {
          return true;
        } else if (s is SetComprehension) {
          return true;
        }
        return false;
      }

      private static readonly Dictionary<string, string> NullaryAttributesToTranslate;

      private static readonly HashSet<string> NullaryAttributesToCopy = [
        .. new[] {
          "focus",
          "isolate",
          "ignore",
          "selective_checking",
          "split",
          "split_here",
          "start_checking_here",
          "testEntry",
          "testInline",
          "vcs_split_on_every_assert",
        }
      ];

      private static readonly HashSet<string> BooleanAttributesToCopy = [
        .. new[] {
          "verify"
        }
      ];

      private static readonly HashSet<string> IntegerAttributesToCopy = [
        .. new[] {
          "subsumption",
          "testInline",
          "timeLimit",
          "vcs_max_cost",
          "vcs_max_keep_going_splits",
          "vcs_max_splits",
          "weight"
        }
      ];

      private static readonly HashSet<string> StringAttributesToCopy = [
        .. new[] {
          "captureState",
          "isolate",
          "error"
        }
      ];

      static ExpressionTranslator() {
        NullaryAttributesToTranslate = new() {
          {
            "isolate_assertions",
            "vcs_split_on_every_assert"
          }
        };
      }

      private QKeyValue TrBooleanAttribute(string name, Expression arg, QKeyValue rest) {
        var boolArg = RemoveLit(TrExpr(arg));
        return boolArg is Boogie.LiteralExpr { IsTrue: true } or Boogie.LiteralExpr { IsFalse: true }
          ? new QKeyValue(arg.Origin, name, new List<object> { boolArg }, rest)
          : rest;
      }

      private QKeyValue TrIntegerAttribute(string name, Expression arg, QKeyValue rest) {
        var intArg = RemoveLit(TrExpr(arg));
        return intArg is Boogie.LiteralExpr { isBigNum: true }
          ? new QKeyValue(arg.Origin, name, new List<object> { intArg }, rest)
          : rest;
      }

      private QKeyValue TrStringAttribute(string name, Expression arg, QKeyValue rest) {
        // pass string literals down to Boogie as string literals, not as their expression translation
        var strArg = arg.AsStringLiteral();
        return strArg is not null
          ? new QKeyValue(arg.Origin, name, new List<object> { strArg }, rest)
          : rest;
      }

      public QKeyValue TrAttributes(Attributes attrs, string skipThisAttribute = null) {
        QKeyValue kv = null;
        var hasNewTimeLimit = Attributes.Contains(attrs, "_timeLimit");
        var hasNewRLimit = Attributes.Contains(attrs, "_rlimit");
        foreach (var attr in attrs.AsEnumerable()) {
          var name = attr.Name;
          if ((name == skipThisAttribute) ||
              // omit the extern attribute when /noExterns option is specified.
              (name is "extern" && options.DisallowExterns) ||
              (name is "timeLimit" && hasNewTimeLimit) ||
              (name is "rlimit" && hasNewRLimit) ||
              (attr is UserSuppliedAtAttribute)
          ) {
            continue;
          }

          if (NullaryAttributesToTranslate.ContainsKey(name) && attr.Args.Count == 0) {
            kv = new QKeyValue(attr.Origin, NullaryAttributesToTranslate[name], new List<object>(), kv);
          } else if (NullaryAttributesToCopy.Contains(name) && attr.Args.Count == 0) {
            kv = new QKeyValue(attr.Origin, name, new List<object>(), kv);
          } else if (BooleanAttributesToCopy.Contains(name) && attr.Args.Count == 1) {
            kv = TrBooleanAttribute(name, attr.Args[0], kv);
          } else if (IntegerAttributesToCopy.Contains(name) && attr.Args.Count == 1) {
            kv = TrIntegerAttribute(name, attr.Args[0], kv);
          } else if (StringAttributesToCopy.Contains(name) && attr.Args.Count == 1) {
            kv = TrStringAttribute(name, attr.Args[0], kv);
          } else if (name is "_timeLimit") {
            kv = TrIntegerAttribute("timeLimit", attr.Args[0], kv);
          } else if (name is "_rlimit") {
            kv = TrIntegerAttribute("rlimit", attr.Args[0], kv);
          } else if (name is "synthesize" or "extern") {
            kv = new QKeyValue(attr.Origin, "extern", new List<object>(), kv);
          } else if (name is "rlimit" && attr.Args.Count == 1) {
            // Values for _rlimit are already in terms of Boogie units (1000 x user-provided value) because they're
            // derived from command-line rlimit settings. Values for rlimit still need to be multiplied.
            if (RemoveLit(TrExpr(attr.Args[0])) is not Boogie.LiteralExpr { isBigNum: true } litExpr) {
              continue;
            }

            var limit = new Boogie.LiteralExpr(
              litExpr.tok,
              BigNum.FromUInt(Boogie.Util.BoundedMultiply((uint)litExpr.asBigNum.ToIntSafe, 1000)),
              litExpr.Immutable);
            kv = new QKeyValue(attr.Origin, name, new List<object> { limit }, kv);
          } else if (name is "resource_limit" && attr.Args.Count == 1) {
            // Do this after the above multiplication because :resource_limit should not be multiplied.
            Expr limit;
            var arg = attr.Args[0];
            var strArg = arg.AsStringLiteral();
            if (strArg != null) {
              if (DafnyOptions.TryParseResourceCount(strArg, out var resourceLimit)) {
                limit = new Boogie.LiteralExpr(attr.Origin, BigNum.FromUInt(resourceLimit), true);
              } else {
                BoogieGenerator.reporter.Error(MessageSource.Verifier, attr.Origin,
                  $"failed to parse resource count: {strArg}");
                continue;
              }
            } else {
              limit = RemoveLit(TrExpr(arg));
            }
            kv = new QKeyValue(attr.Origin, "rlimit", new List<object> { limit }, kv);
          }
        }
        return kv;
      }

      // --------------- help routines ---------------

      public Boogie.Expr IsAlloced(IOrigin tok, Boogie.Expr e) {
        Contract.Requires(HeapExpr != null);
        return BoogieGenerator.IsAlloced(tok, HeapExpr, e);
      }

      public Boogie.Expr GoodRef(IOrigin tok, Boogie.Expr e, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        // Add $Is and $IsAlloc
        return BoogieGenerator.GetWhereClause(tok, e, type, this, ISALLOC);
      }

      public Expression MakeAllowance(FunctionCallExpr e, CanCallOptions cco = null) {
        Expression allowance = Expression.CreateBoolLiteral(e.Origin, true);
        if (!e.Function.IsStatic) {
          var formalThis = new ThisExpr(cco == null ? e.Function : cco.EnclosingFunction);
          allowance = Expression.CreateAnd(allowance, Expression.CreateEq(e.Receiver, formalThis, e.Receiver.Type));
        }
        var formals = cco == null ? e.Function.Ins : cco.EnclosingFunction.Ins;
        for (int i = 0; i < e.Args.Count; i++) {
          Expression ee = e.Args[i];
          Formal ff = formals[i];
          allowance = Expression.CreateAnd(allowance, Expression.CreateEq(ee, Expression.CreateIdentExpr(ff), ff.Type));
        }
        return allowance;
      }

      public Expr CanCallAssumption(Expression expr, CanCallOptions cco = null) {
        Contract.Requires(expr != null);
        Contract.Requires(this != null);
        Contract.Requires(BoogieGenerator.Predef != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        if (expr is LiteralExpr || expr is ThisExpr || expr is IdentifierExpr || expr is WildcardExpr || expr is BoogieWrapper) {
          return Boogie.Expr.True;
        } else if (expr is DisplayExpression) {
          DisplayExpression e = (DisplayExpression)expr;
          return CanCallAssumption(e.Elements, cco);
        } else if (expr is MapDisplayExpr) {
          MapDisplayExpr e = (MapDisplayExpr)expr;
          List<Expression> l = [];
          foreach (MapDisplayEntry p in e.Elements) {
            l.Add(p.A); l.Add(p.B);
          }
          return CanCallAssumption(l, cco);
        } else if (expr is MemberSelectExpr) {
          MemberSelectExpr e = (MemberSelectExpr)expr;
          var r = CanCallAssumption(e.Obj, cco);
          if (e.Member is DatatypeDestructor) {
            var dtor = (DatatypeDestructor)e.Member;
            if (dtor.EnclosingCtors.Count == dtor.EnclosingCtors[0].EnclosingDatatype.Ctors.Count) {
              // Every constructor has this destructor; might as well assume that here.
              var correctConstructor = BplOr(dtor.EnclosingCtors.ConvertAll(
                ctor => FunctionCall(e.Origin, ctor.QueryField.FullSanitizedName, Boogie.Type.Bool, TrExpr(e.Obj))));
              r = BplAnd(r, correctConstructor);
            }
          } else if (e.Member is ConstantField { Rhs: { } rhs } && BoogieGenerator.RevealedInScope(e.Member)) {
            r = CanCallAssumption(Substitute(rhs, e.Obj, new Dictionary<IVariable, Expression>(), null));
          }
          return r;
        } else if (expr is SeqSelectExpr) {
          SeqSelectExpr e = (SeqSelectExpr)expr;
          Boogie.Expr total = CanCallAssumption(e.Seq, cco);
          if (e.E0 != null) {
            total = BplAnd(total, CanCallAssumption(e.E0, cco));
          }
          if (e.E1 != null) {
            total = BplAnd(total, CanCallAssumption(e.E1, cco));
          }
          return total;
        } else if (expr is MultiSelectExpr) {
          MultiSelectExpr e = (MultiSelectExpr)expr;
          Boogie.Expr total = CanCallAssumption(e.Array, cco);
          foreach (Expression idx in e.Indices) {
            total = BplAnd(total, CanCallAssumption(idx, cco));
          }
          return total;
        } else if (expr is SeqUpdateExpr) {
          SeqUpdateExpr e = (SeqUpdateExpr)expr;
          Boogie.Expr total = CanCallAssumption(e.Seq, cco);
          total = BplAnd(total, CanCallAssumption(e.Index, cco));
          total = BplAnd(total, CanCallAssumption(e.Value, cco));
          return total;

        } else if (expr is ApplyExpr) {
          ApplyExpr e = (ApplyExpr)expr;

          Func<Expression, Boogie.Expr> TrArg = arg => {
            Boogie.Expr inner = TrExpr(arg);
            if (ModeledAsBoxType(arg.Type)) {
              return inner;
            } else {
              return BoogieGenerator.FunctionCall(arg.Origin, BuiltinFunction.Box, null, inner);
            }
          };

          var args = Concat(
            Map(e.Function.Type.AsArrowType.TypeArgs, BoogieGenerator.TypeToTy),
            Cons(HeapExpr,
              Cons(TrExpr(e.Function),
                e.Args.ConvertAll(arg => TrArg(arg)))));

          var requiresk = FunctionCall(e.Origin, Requires(e.Args.Count), Boogie.Type.Bool, args);
          return BplAnd(
            BplAnd(
              Cons(CanCallAssumption(e.Function, cco),
                e.Args.ConvertAll(ee => CanCallAssumption(ee, cco)))),
            requiresk);

        } else if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          Boogie.Expr r = CanCallAssumption(e.Receiver, cco);
          r = BplAnd(r, CanCallAssumption(e.Args, cco));
          if (!(e.Function is SpecialFunction)) {
            Boogie.IdentifierExpr canCallFuncID = new Boogie.IdentifierExpr(expr.Origin, e.Function.FullSanitizedName + "#canCall", Boogie.Type.Bool);
            List<Boogie.Expr> args = FunctionInvocationArguments(e, null, null);
            Boogie.Expr canCallFuncAppl = new Boogie.NAryExpr(BoogieGenerator.GetToken(expr), new Boogie.FunctionCall(canCallFuncID), args);
            var add = cco != null && cco.MakeAllowance(e.Function) ? Boogie.Expr.Or(TrExpr(MakeAllowance(e, cco)), canCallFuncAppl) : canCallFuncAppl;
            r = BplAnd(r, add);
          }
          return r;
        } else if (expr is DatatypeValue) {
          DatatypeValue dtv = (DatatypeValue)expr;
          return CanCallAssumption(dtv.Arguments, cco);
        } else if (expr is SeqConstructionExpr) {
          var e = (SeqConstructionExpr)expr;
          // CanCallAssumption[[ seq(n, init) ]] =
          //     CanCallAssumption[[ n ]] &&
          //     CanCallAssumption[[ init ]] &&
          //     var initF := init; // necessary, in order to use init(i) in trigger, since it may contain quantifiers
          //     (forall i: int
          //         { initF(i) }
          //         0 <= i < n ==>
          //             CanCallAssumption[[ init(i) ]])

          var varNameGen = BoogieGenerator.CurrentIdGenerator.NestedFreshIdGenerator("seqinit$");
          var indexVar = new Bpl.BoundVariable(e.Origin, new Bpl.TypedIdent(e.Origin, varNameGen.FreshId("#i"), Bpl.Type.Int));
          var index = new Bpl.IdentifierExpr(e.Origin, indexVar);
          var indexRange = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), index), Bpl.Expr.Lt(index, TrExpr(e.N)));
          var initFVar = new Bpl.BoundVariable(e.Origin, new Bpl.TypedIdent(e.Origin, varNameGen.FreshId("#f"), Predef.HandleType));

          var initF = new Bpl.IdentifierExpr(e.Origin, initFVar);

          var dafnyInitApplication = new ApplyExpr(e.Origin, e.Initializer,
            [new BoogieWrapper(index, Type.Int)],
            Token.NoToken) {
            Type = e.Initializer.Type.AsArrowType.Result
          };
          var canCall = CanCallAssumption(dafnyInitApplication);

          dafnyInitApplication = new ApplyExpr(e.Origin, new BoogieWrapper(initF, e.Initializer.Type),
            [new BoogieWrapper(index, Type.Int)],
            Token.NoToken) {
            Type = e.Initializer.Type.AsArrowType.Result
          };
          var apply = TrExpr(dafnyInitApplication);

          var tr = new Bpl.Trigger(e.Origin, true, new List<Bpl.Expr> { apply });
          var ccaInit = new Bpl.ForallExpr(e.Origin, [indexVar], tr, BplImp(indexRange, canCall));
          var rhsAppliedToIndex = new Bpl.LetExpr(e.Origin, [initFVar],
            [TrExpr(e.Initializer)], null, ccaInit);

          return BplAnd(BplAnd(CanCallAssumption(e.N, cco), CanCallAssumption(e.Initializer, cco)), rhsAppliedToIndex);

        } else if (expr is MultiSetFormingExpr) {
          MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
          return CanCallAssumption(e.E, cco);
        } else if (expr is OldExpr) {
          var e = (OldExpr)expr;
          return OldAt(e.AtLabel).CanCallAssumption(e.Expr, cco);
        } else if (expr is UnchangedExpr) {
          var e = (UnchangedExpr)expr;
          Boogie.Expr be = Boogie.Expr.True;
          foreach (var fe in e.Frame) {
            be = BplAnd(be, CanCallAssumption(fe.E, cco));
          }
          return be;
        } else if (expr is UnaryExpr) {
          var e = (UnaryExpr)expr;
          return CanCallAssumption(e.E, cco);
        } else if (expr is BinaryExpr) {
          // The short-circuiting boolean operators &&, ||, and ==> end up duplicating their
          // left argument. Therefore, we first try to re-associate the expression to make
          // left arguments smaller.
          if (BoogieGenerator.ReAssociateToTheRight(ref expr)) {
            return CanCallAssumption(expr, cco);
          }
          var e = (BinaryExpr)expr;

          Boogie.Expr t0 = CanCallAssumption(e.E0, cco);
          Boogie.Expr t1 = CanCallAssumption(e.E1, cco);
          switch (e.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.And:
            case BinaryExpr.ResolvedOpcode.Imp:
              t1 = BplImp(TrExpr(e.E0), t1);
              break;
            case BinaryExpr.ResolvedOpcode.Or:
              t1 = BplImp(Boogie.Expr.Not(TrExpr(e.E0)), t1);
              break;
            case BinaryExpr.ResolvedOpcode.EqCommon:
            case BinaryExpr.ResolvedOpcode.NeqCommon: {
                Boogie.Expr r = Boogie.Expr.True;
                if (cco is not { SkipIsA: true }) {
                  if (e.E0 is { Type: { AsDatatype: { } dt0 }, Resolved: not DatatypeValue }) {
                    var funcID = new Boogie.FunctionCall(new Boogie.IdentifierExpr(expr.Origin, "$IsA#" + dt0.FullSanitizedName, Boogie.Type.Bool));
                    r = BplAnd(r, new Boogie.NAryExpr(expr.Origin, funcID, new List<Boogie.Expr> { TrExpr(e.E0) }));
                  }
                  if (e.E1 is { Type: { AsDatatype: { } dt1 }, Resolved: not DatatypeValue }) {
                    var funcID = new Boogie.FunctionCall(new Boogie.IdentifierExpr(expr.Origin, "$IsA#" + dt1.FullSanitizedName, Boogie.Type.Bool));
                    r = BplAnd(r, new Boogie.NAryExpr(expr.Origin, funcID, new List<Boogie.Expr> { TrExpr(e.E1) }));
                  }
                }
                return BplAnd(r, BplAnd(t0, t1));
              }
            case BinaryExpr.ResolvedOpcode.Mul:
              if (7 <= BoogieGenerator.options.ArithMode) {
                if (e.E0.Type.IsNumericBased(Type.NumericPersuasion.Int) && !BoogieGenerator.DisableNonLinearArithmetic) {
                  // Produce a useful fact about the associativity of multiplication. It is a bit dicey to do as an axiom.
                  // Change (k*A)*B or (A*k)*B into (A*B)*k, where k is a numeric literal
                  var left = e.E0.Resolved as BinaryExpr;
                  if (left != null && left.ResolvedOp == BinaryExpr.ResolvedOpcode.Mul) {
                    Boogie.Expr r = Boogie.Expr.True;
                    if (left.E0.Resolved is LiteralExpr) {
                      // (K*A)*B == (A*B)*k
                      var y = Expression.CreateMul(Expression.CreateMul(left.E1, e.E1), left.E0);
                      var eq = Expression.CreateEq(e, y, e.E0.Type);
                      r = BplAnd(r, TrExpr(eq));
                    }
                    if (left.E1.Resolved is LiteralExpr) {
                      // (A*k)*B == (A*B)*k
                      var y = Expression.CreateMul(Expression.CreateMul(left.E0, e.E1), left.E1);
                      var eq = Expression.CreateEq(e, y, e.E0.Type);
                      r = BplAnd(r, TrExpr(eq));
                    }
                    if (r != Boogie.Expr.True) {
                      return BplAnd(BplAnd(t0, t1), r);
                    }
                  }
                }
              }
              break;
            default:
              break;
          }
          return BplAnd(t0, t1);
        } else if (expr is TernaryExpr) {
          var e = (TernaryExpr)expr;
          return BplAnd(CanCallAssumption(e.E0, cco), BplAnd(CanCallAssumption(e.E1, cco), CanCallAssumption(e.E2, cco)));

        } else if (expr is LetExpr letExpr) {
          return LetCanCallAssumption(letExpr, cco);

        } else if (expr is LambdaExpr) {
          var e = (LambdaExpr)expr;

          var bvarsAndAntecedents = new List<Tuple<Boogie.Variable, Boogie.Expr>>();
          var varNameGen = BoogieGenerator.CurrentIdGenerator.NestedFreshIdGenerator("$l#");

          Boogie.Expr heap; var hVar = BplBoundVar(varNameGen.FreshId("#heap#"), BoogieGenerator.Predef.HeapType, out heap);
          var et = this.HeapExpr != null
            ? new ExpressionTranslator(this.BoogieGenerator, this.Predef, heap, this.Old.HeapExpr, this.scope)
            : new ExpressionTranslator(this, heap);

          Dictionary<IVariable, Expression> subst = new Dictionary<IVariable, Expression>();
          foreach (var bv in e.BoundVars) {
            Boogie.Expr ve; var yVar = BplBoundVar(varNameGen.FreshId(string.Format("#{0}#", bv.Name)), BoogieGenerator.TrType(bv.Type), out ve);
            var wh = BoogieGenerator.GetWhereClause(bv.Origin, new Boogie.IdentifierExpr(bv.Origin, yVar), bv.Type, et, NOALLOC);
            bvarsAndAntecedents.Add(Tuple.Create<Boogie.Variable, Boogie.Expr>(yVar, wh));
            subst[bv] = new BoogieWrapper(ve, bv.Type);
          }

          var canCall = et.CanCallAssumption(Substitute(e.Body, null, subst), cco);
          if (e.Range != null) {
            var range = Substitute(e.Range, null, subst);
            canCall = BplAnd(CanCallAssumption(range, cco), BplImp(TrExpr(range), canCall));
          }

          // It's important to add the heap last to "bvarsAndAntecedents", because the heap may occur in the antecedents of
          // the other variables and BplForallTrim processes the given tuples in order.
          var goodHeap = BoogieGenerator.FunctionCall(e.Origin, BuiltinFunction.IsGoodHeap, null, heap);
          bvarsAndAntecedents.Add(Tuple.Create<Boogie.Variable, Boogie.Expr>(hVar, goodHeap));

          //TRIG (forall $l#0#heap#0: Heap, $l#0#x#0: int :: true)
          //TRIG (forall $l#0#heap#0: Heap, $l#0#t#0: DatatypeType :: _module.__default.TMap#canCall(_module._default.TMap$A, _module._default.TMap$B, $l#0#heap#0, $l#0#t#0, f#0))
          //TRIG (forall $l#4#heap#0: Heap, $l#4#x#0: Box :: _0_Monad.__default.Bind#canCall(Monad._default.Associativity$B, Monad._default.Associativity$C, $l#4#heap#0, Apply1(Monad._default.Associativity$A, #$M$B, f#0, $l#4#heap#0, $l#4#x#0), g#0))
          return BplForallTrim(bvarsAndAntecedents, null, canCall); // L_TRIGGER

        } else if (expr is ComprehensionExpr) {
          var e = (ComprehensionExpr)expr;
          if (e is QuantifierExpr q && q.SplitQuantifier != null) {
            return CanCallAssumption(q.SplitQuantifierExpression, cco);
          }

          // Determine the CanCall's for the range and term
          var canCall = CanCallAssumption(e.Term, cco);
          if (e.Range != null) {
            canCall = BplAnd(CanCallAssumption(e.Range, cco), BplImp(TrExpr(e.Range), canCall));
          }
          if (expr is MapComprehension mc && mc.IsGeneralMapComprehension) {
            canCall = BplAnd(canCall, CanCallAssumption(mc.TermLeft, cco));

            // The translation of "map x,y | R(x,y) :: F(x,y) := G(x,y)" makes use of projection
            // functions project_x,project_y.  These are functions defined here by the following axiom:
            //     forall x,y :: R(x,y) ==> var x',y' := project_x(F(x,y)),project_y(F(x,y)); R(x',y') && F(x',y') == F(x,y)
            // that is (without the let expression):
            //     forall x,y :: R(x,y) ==> R(project_x(F(x,y)), project_y(F(x,y))) && F(project_x(F(x,y)), project_y(F(x,y))) == F(x,y)
            // The triggers for the quantification are those detected for the given map comprehension, if any.
            List<Boogie.Variable> bvs;
            List<Boogie.Expr> args;
            BoogieGenerator.CreateBoundVariables(mc.BoundVars, out bvs, out args);
            Contract.Assert(mc.BoundVars.Count == bvs.Count);
            BoogieGenerator.CreateMapComprehensionProjectionFunctions(mc);
            Contract.Assert(mc.ProjectionFunctions != null);
            Contract.Assert(mc.ProjectionFunctions.Count == mc.BoundVars.Count);
            var substMap = new Dictionary<IVariable, Expression>();
            for (var i = 0; i < mc.BoundVars.Count; i++) {
              substMap.Add(mc.BoundVars[i], new BoogieWrapper(args[i], mc.BoundVars[i].Type));
            }
            var R = TrExpr(Substitute(mc.Range, null, substMap));
            var F = TrExpr(Substitute(mc.TermLeft, null, substMap));
            var trig = BoogieGenerator.TrTrigger(this, e.Attributes, expr.Origin, substMap);
            substMap = new Dictionary<IVariable, Expression>();
            for (var i = 0; i < mc.BoundVars.Count; i++) {
              var p = new Boogie.NAryExpr(BoogieGenerator.GetToken(mc), new Boogie.FunctionCall(mc.ProjectionFunctions[i]), new List<Boogie.Expr> { F });
              substMap.Add(e.BoundVars[i], new BoogieWrapper(p, e.BoundVars[i].Type));
            }
            var Rprime = TrExpr(Substitute(mc.Range, null, substMap));
            var Fprime = TrExpr(Substitute(mc.TermLeft, null, substMap));
            var defn = BplForall(bvs, trig, BplImp(R, BplAnd(Rprime, Boogie.Expr.Eq(F, Fprime))));
            canCall = BplAnd(canCall, defn);
          }
          // Create a list of all possible bound variables
          var bvarsAndAntecedents = TrBoundVariables_SeparateWhereClauses(e.BoundVars);
          // Produce the quantified CanCall expression, with a suitably reduced set of bound variables
          var tr = BoogieGenerator.TrTrigger(this, e.Attributes, expr.Origin);
          return BplForallTrim(bvarsAndAntecedents, tr, canCall);

        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          return CanCallAssumption(e.E, cco);
        } else if (expr is ITEExpr) {
          ITEExpr e = (ITEExpr)expr;
          Boogie.Expr total = CanCallAssumption(e.Test, cco);
          Boogie.Expr test = TrExpr(e.Test);
          total = BplAnd(total, BplImp(test, CanCallAssumption(e.Thn, cco)));
          total = BplAnd(total, BplImp(Boogie.Expr.Not(test), CanCallAssumption(e.Els, cco)));
          return total;
        } else if (expr is ConcreteSyntaxExpression) {
          var e = (ConcreteSyntaxExpression)expr;
          return CanCallAssumption(e.ResolvedExpression, cco);
        } else if (expr is NestedMatchExpr nestedMatchExpr) {
          return CanCallAssumption(nestedMatchExpr.Flattened, cco);
        } else if (expr is BoogieFunctionCall) {
          var e = (BoogieFunctionCall)expr;
          return CanCallAssumption(e.Args, cco);
        } else if (expr is MatchExpr) {
          var e = (MatchExpr)expr;
          var ite = DesugarMatchExpr(e);
          return CanCallAssumption(ite, cco);
        } else if (expr is BoxingCastExpr) {
          var e = (BoxingCastExpr)expr;
          return CanCallAssumption(e.E, cco);
        } else if (expr is UnboxingCastExpr) {
          var e = (UnboxingCastExpr)expr;
          return CanCallAssumption(e.E, cco);
        } else if (expr is DecreasesToExpr decreasesToExpr) {
          var oldCanCall = CanCallAssumption(decreasesToExpr.OldExpressions.ToList(), cco);
          var newCanCall = CanCallAssumption(decreasesToExpr.NewExpressions.ToList(), cco);
          return BplAnd(oldCanCall, newCanCall);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
        }
      }

      public Expr CanCallAssumption(List<Expression> exprs, CanCallOptions cco) {
        Contract.Requires(this != null);
        Contract.Requires(exprs != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        Boogie.Expr total = Boogie.Expr.True;
        foreach (Expression e in exprs) {
          Contract.Assert(e != null);
          total = BplAnd(total, CanCallAssumption(e, cco));
        }
        return total;
      }
    }

    public class CanCallOptions {
      public bool SkipIsA;

      public readonly Function EnclosingFunction; // self-call allowance is applied to the enclosing function
      public readonly bool SelfCallAllowanceAlsoForOverride;

      public bool MakeAllowance(Function f) {
        return f == EnclosingFunction || (SelfCallAllowanceAlsoForOverride && f == EnclosingFunction.OverriddenFunction);
      }

      public CanCallOptions(bool skipIsA, Function enclosingFunction, bool selfCallAllowanceAlsoForOverride = false) {
        Contract.Assert(!selfCallAllowanceAlsoForOverride ||
                        (enclosingFunction.OverriddenFunction != null &&
                         enclosingFunction.Ins.Count == enclosingFunction.OverriddenFunction.Ins.Count));
        this.SkipIsA = skipIsA;
        this.EnclosingFunction = enclosingFunction;
        this.SelfCallAllowanceAlsoForOverride = selfCallAllowanceAlsoForOverride;
      }
    }
  }
}
