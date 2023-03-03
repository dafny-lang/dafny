using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;

namespace Microsoft.Dafny {
  public partial class Translator {

    internal class ExpressionTranslator {
      // HeapExpr == null ==> translation of pure (no-heap) expression
      readonly Boogie.Expr _the_heap_expr;
      public Boogie.Expr HeapExpr {
        // The increment of Statistics_HeapUses in the following line is a hack and not entirely a good idea.
        // Not only does one need to be careful not to mention HeapExpr in contracts (in particular, in ObjectInvariant()
        // below), but also, the debugger may invoke HeapExpr and that will cause an increment as well.
        get { Statistics_HeapUses++; return _the_heap_expr; }
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

      public readonly PredefinedDecls predef;
      public readonly Translator translator;
      public readonly string This;
      public readonly string modifiesFrame; // the name of the context's frame variable.
      readonly Function applyLimited_CurrentFunction;
      public readonly FuelSetting layerInterCluster;
      public readonly FuelSetting layerIntraCluster = null;  // a value of null says to do the same as for inter-cluster calls
      public int Statistics_CustomLayerFunctionCount = 0;
      public int Statistics_HeapAsQuantifierCount = 0;
      public int Statistics_HeapUses = 0;
      public readonly bool stripLits = false;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        // In the following line, it is important to use _the_heap_expr directly, rather than HeapExpr, because
        // the HeapExpr getter has a side effect on Statistics_HeapUses.
        Contract.Invariant(_the_heap_expr == null || _the_heap_expr is Boogie.OldExpr || _the_heap_expr is Boogie.IdentifierExpr);
        Contract.Invariant(predef != null);
        Contract.Invariant(translator != null);
        Contract.Invariant(This != null);
        Contract.Invariant(modifiesFrame != null);
        Contract.Invariant(layerInterCluster != null);
        Contract.Invariant(0 <= Statistics_CustomLayerFunctionCount);
      }

      /// <summary>
      /// This is the most general constructor.  It is private and takes all the parameters.  Whenever
      /// one ExpressionTranslator is constructed from another, unchanged parameters are just copied in.
      /// </summary>
      ExpressionTranslator(Translator translator, PredefinedDecls predef, Boogie.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, FuelSetting layerInterCluster, FuelSetting layerIntraCluster, string modifiesFrame, bool stripLits) {

        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(thisVar != null);
        Contract.Requires(modifiesFrame != null);

        this.translator = translator;
        this.predef = predef;
        this._the_heap_expr = heap;
        this.This = thisVar;
        this.applyLimited_CurrentFunction = applyLimited_CurrentFunction;
        this.layerInterCluster = layerInterCluster;
        if (layerIntraCluster == null) {
          this.layerIntraCluster = layerInterCluster;
        } else {
          this.layerIntraCluster = layerIntraCluster;
        }
        this.modifiesFrame = modifiesFrame;
        this.stripLits = stripLits;
      }

      public static Boogie.IdentifierExpr HeapIdentifierExpr(PredefinedDecls predef, Boogie.IToken heapToken) {
        return new Boogie.IdentifierExpr(heapToken, predef.HeapVarName, predef.HeapType);
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Boogie.IToken heapToken)
        : this(translator, predef, HeapIdentifierExpr(predef, heapToken)) {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heapToken != null);
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Boogie.Expr heap)
        : this(translator, predef, heap, "this") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Boogie.Expr heap, Boogie.Expr oldHeap)
        : this(translator, predef, heap, "this") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(oldHeap != null);

        var old = new ExpressionTranslator(translator, predef, oldHeap);
        old.oldEtran = old;
        this.oldEtran = old;
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Boogie.Expr heap, string thisVar)
        : this(translator, predef, heap, thisVar, null, new FuelSetting(translator, 1), null, "$_Frame", false) {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(thisVar != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, Boogie.Expr heap)
        : this(etran.translator, etran.predef, heap, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, etran.modifiesFrame, etran.stripLits) {
        Contract.Requires(etran != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, string modifiesFrame)
        : this(etran.translator, etran.predef, etran.HeapExpr, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, modifiesFrame, etran.stripLits) {
        Contract.Requires(etran != null);
        Contract.Requires(modifiesFrame != null);
      }

      internal IToken GetToken(Expression expression) {
        return translator.GetToken(expression);
      }

      ExpressionTranslator oldEtran;
      public ExpressionTranslator Old {
        get {
          Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

          if (oldEtran == null) {
            oldEtran = new ExpressionTranslator(translator, predef, new Boogie.OldExpr(HeapExpr.tok, HeapExpr), This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
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
        var heapAt = new Boogie.IdentifierExpr(Token.NoToken, "$Heap_at_" + label.AssignUniqueId(translator.CurrentIdGenerator), predef.HeapType);
        return new ExpressionTranslator(translator, predef, heapAt, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
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

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, null, new FuelSetting(translator, 0, layerArgument), new FuelSetting(translator, 0, layerArgument), modifiesFrame, stripLits);
      }

      public ExpressionTranslator WithCustomFuelSetting(CustomFuelSettings customSettings) {
        // Use the existing layers but with some per-function customizations
        Contract.Requires(customSettings != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, null, layerInterCluster.WithContext(customSettings), layerIntraCluster.WithContext(customSettings), modifiesFrame, stripLits);
      }

      public ExpressionTranslator ReplaceLayer(Boogie.Expr layerArgument) {
        // different layer with same fuel amount.
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.WithLayer(layerArgument), layerIntraCluster.WithLayer(layerArgument), modifiesFrame, stripLits);
      }

      public ExpressionTranslator WithNoLits() {
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);
        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, true);
      }

      public ExpressionTranslator LimitedFunctions(Function applyLimited_CurrentFunction, Boogie.Expr layerArgument) {
        Contract.Requires(applyLimited_CurrentFunction != null);
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, /* layerArgument */ layerInterCluster, new FuelSetting(translator, 0, layerArgument), modifiesFrame, stripLits);
      }

      public ExpressionTranslator LayerOffset(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.Offset(offset), layerIntraCluster, modifiesFrame, stripLits);
      }

      public ExpressionTranslator DecreaseFuel(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.Decrease(offset), layerIntraCluster, modifiesFrame, stripLits);
      }

      private static ExpressionTranslator CloneExpressionTranslator(ExpressionTranslator orig,
        Translator translator, PredefinedDecls predef, Boogie.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, FuelSetting layerInterCluster, FuelSetting layerIntraCluster, string modifiesFrame, bool stripLits) {
        var et = new ExpressionTranslator(translator, predef, heap, thisVar, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
        if (orig.oldEtran != null) {
          var etOld = new ExpressionTranslator(translator, predef, orig.Old.HeapExpr, thisVar, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
          etOld.oldEtran = etOld;
          et.oldEtran = etOld;
        }
        return et;
      }

      public Boogie.IdentifierExpr TheFrame(IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>().Type != null);

        Boogie.TypeVariable alpha = new Boogie.TypeVariable(tok, "beta");
        Boogie.Type fieldAlpha = predef.FieldName(tok, alpha);
        Boogie.Type ty = new Boogie.MapType(tok, new List<TypeVariable> { alpha }, new List<Boogie.Type> { predef.RefType, fieldAlpha }, Boogie.Type.Bool);
        return new Boogie.IdentifierExpr(tok, this.modifiesFrame, ty);
      }

      public Boogie.IdentifierExpr Tick() {
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>().Type != null);
        return new Boogie.IdentifierExpr(Token.NoToken, "$Tick", predef.TickType);
      }

      public Boogie.IdentifierExpr ArbitraryBoxValue() {
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>() != null);
        return new Boogie.IdentifierExpr(Token.NoToken, "$ArbitraryBoxValue", predef.BoxType);
      }
      public Boogie.Expr ArbitraryValue(Type type) {
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);
        var bx = ArbitraryBoxValue();
        if (!ModeledAsBoxType(type)) {
          return translator.FunctionCall(Token.NoToken, BuiltinFunction.Unbox, translator.TrType(type), bx);
        } else {
          return bx;
        }
      }

      public Boogie.IdentifierExpr FunctionContextHeight() {
        Contract.Ensures(Contract.Result<Boogie.IdentifierExpr>().Type != null);
        return new Boogie.IdentifierExpr(Token.NoToken, "$FunctionContextHeight", Boogie.Type.Int);
      }

      public Boogie.Expr HeightContext(ICallable m) {
        Contract.Requires(m != null);
        // free requires fh == FunctionContextHeight;
        var module = m.EnclosingModule;
        Boogie.Expr context =
          Boogie.Expr.Eq(Boogie.Expr.Literal(module.CallGraph.GetSCCRepresentativePredecessorCount(m)), FunctionContextHeight());
        return context;
      }

      public Expression GetSubstitutedBody(LetExpr e) {
        Contract.Requires(e != null);
        Contract.Requires(e.Exact);
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < e.LHSs.Count; i++) {
          translator.AddCasePatternVarSubstitutions(e.LHSs[i], TrExpr(e.RHSs[i]), substMap);
        }
        return Translator.Substitute(e.Body, null, substMap);
      }

      public Expr MaybeLit(Expr expr, Boogie.Type type) {
        return stripLits ? expr : translator.Lit(expr, type);
      }

      public Expr MaybeLit(Expr expr) {
        return stripLits ? expr : translator.Lit(expr);
      }

      /// <summary>
      /// Translates Dafny expression "expr" into a Boogie expression.  If the type of "expr" can be a boolean, then the
      /// token (source location) of the resulting expression is filled in (it wouldn't hurt if the token were always
      /// filled in, but it is really necessary for anything that may show up in a Boogie assert, since that location may
      /// then show up in an error message).
      /// </summary>
      public Boogie.Expr TrExpr(Expression expr) {
        Contract.Requires(expr != null);
        Contract.Requires(predef != null);

        if (expr is LiteralExpr) {
          LiteralExpr e = (LiteralExpr)expr;
          if (e.Value == null) {
            return predef.Null;
          } else if (e.Value is bool) {
            return MaybeLit(new Boogie.LiteralExpr(GetToken(e), (bool)e.Value));
          } else if (e is CharLiteralExpr) {
            // we expect e.Value to be a string representing exactly one char
            Boogie.Expr rawElement = null;  // assignment to please compiler's definite assignment rule
            foreach (var ch in Util.UnescapedCharacters((string)e.Value, false)) {
              Contract.Assert(rawElement == null);  // we should get here only once
              rawElement = translator.FunctionCall(GetToken(expr), BuiltinFunction.CharFromInt, null, Boogie.Expr.Literal(ch));
            }
            Contract.Assert(rawElement != null);  // there should have been an iteration of the loop above
            return MaybeLit(rawElement, predef.CharType);
          } else if (e is StringLiteralExpr) {
            var str = (StringLiteralExpr)e;
            Boogie.Expr seq = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqEmpty, predef.BoxType);
            foreach (var ch in Util.UnescapedCharacters((string)e.Value, str.IsVerbatim)) {
              var rawElement = translator.FunctionCall(GetToken(expr), BuiltinFunction.CharFromInt, null, Boogie.Expr.Literal(ch));
              Boogie.Expr elt = BoxIfNecessary(GetToken(expr), rawElement, Type.Char);
              seq = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqBuild, predef.BoxType, seq, elt);
            }
            return MaybeLit(seq, translator.TrType(new SeqType(Type.Char)));
          } else if (e.Value is BigInteger) {
            var n = Microsoft.BaseTypes.BigNum.FromBigInt((BigInteger)e.Value);
            if (e.Type is BitvectorType) {
              return MaybeLit(translator.BplBvLiteralExpr(GetToken(e), n, e.Type.AsBitVectorType));
            } else if (e.Type.IsBigOrdinalType) {
              var fromNat = FunctionCall(GetToken(expr), "ORD#FromNat", predef.BigOrdinalType, Boogie.Expr.Literal(n));
              return MaybeLit(fromNat, predef.BigOrdinalType);
            } else {
              return MaybeLit(Boogie.Expr.Literal(n));
            }
          } else if (e.Value is BaseTypes.BigDec) {
            return MaybeLit(Boogie.Expr.Literal((BaseTypes.BigDec)e.Value));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
          }

        } else if (expr is ThisExpr) {
          return new Boogie.IdentifierExpr(GetToken(expr), This, translator.TrType(expr.Type));

        } else if (expr is IdentifierExpr) {
          IdentifierExpr e = (IdentifierExpr)expr;
          Contract.Assert(e.Var != null);
          return translator.TrVar(GetToken(expr), e.Var);

        } else if (expr is BoogieWrapper) {
          var e = (BoogieWrapper)expr;
          return e.Expr;


        } else if (expr is BoogieFunctionCall) {
          var e = (BoogieFunctionCall)expr;
          var id = new Boogie.IdentifierExpr(GetToken(e), e.FunctionName, translator.TrType(e.Type));
          var args = new List<Boogie.Expr>();
          foreach (var arg in e.TyArgs) {
            args.Add(translator.TypeToTy(arg));
          }
          if (e.UsesHeap) {
            args.Add(HeapExpr);
          }
          if (e.UsesOldHeap) {
            args.Add(Old.HeapExpr);
          }
          foreach (var heapAtLabel in e.HeapAtLabels) {
            Boogie.Expr ve;
            var bv = BplBoundVar("$Heap_at_" + heapAtLabel.AssignUniqueId(translator.CurrentIdGenerator), translator.predef.HeapType, out ve);
            args.Add(ve);
          }
          foreach (var arg in e.Args) {
            args.Add(TrExpr(arg));
          }
          return new Boogie.NAryExpr(GetToken(e), new Boogie.FunctionCall(id), args);

        } else if (expr is SetDisplayExpr) {
          SetDisplayExpr e = (SetDisplayExpr)expr;
          Boogie.Expr s = translator.FunctionCall(GetToken(expr), e.Finite ? BuiltinFunction.SetEmpty : BuiltinFunction.ISetEmpty, predef.BoxType);
          var isLit = true;
          foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Boogie.Expr ss = BoxIfNecessary(GetToken(expr), rawElement, cce.NonNull(ee.Type));
            s = translator.FunctionCall(GetToken(expr), e.Finite ? BuiltinFunction.SetUnionOne : BuiltinFunction.ISetUnionOne, predef.BoxType, s, ss);
          }
          if (isLit) {
            // Lit-lifting: All elements are lit, so the set is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MultiSetDisplayExpr) {
          MultiSetDisplayExpr e = (MultiSetDisplayExpr)expr;
          Boogie.Expr s = translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetEmpty, predef.BoxType);
          var isLit = true;
          foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Boogie.Expr ss = BoxIfNecessary(GetToken(expr), rawElement, cce.NonNull(ee.Type));
            s = translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetUnionOne, predef.BoxType, s, ss);
          }
          if (isLit) {
            // Lit-lifting: All elements are lit, so the multiset is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is SeqDisplayExpr) {
          SeqDisplayExpr e = (SeqDisplayExpr)expr;
          // Note: a LiteralExpr(string) is really another kind of SeqDisplayExpr
          Boogie.Expr s = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqEmpty, predef.BoxType);
          var isLit = true;
          foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Boogie.Expr elt = BoxIfNecessary(GetToken(expr), rawElement, ee.Type);
            s = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqBuild, predef.BoxType, s, elt);
          }
          if (isLit) {
            // Lit-lifting: All elements are lit, so the sequence is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MapDisplayExpr) {
          MapDisplayExpr e = (MapDisplayExpr)expr;
          Boogie.Type maptype = predef.MapType(GetToken(expr), e.Finite, predef.BoxType, predef.BoxType);
          Boogie.Expr s = translator.FunctionCall(GetToken(expr), e.Finite ? BuiltinFunction.MapEmpty : BuiltinFunction.IMapEmpty, predef.BoxType);
          var isLit = true;
          foreach (ExpressionPair p in e.Elements) {
            var rawA = TrExpr(p.A);
            var rawB = TrExpr(p.B);
            isLit = isLit && translator.IsLit(rawA) && translator.IsLit(rawB);
            Boogie.Expr elt = BoxIfNecessary(GetToken(expr), rawA, cce.NonNull(p.A.Type));
            Boogie.Expr elt2 = BoxIfNecessary(GetToken(expr), rawB, cce.NonNull(p.B.Type));
            s = FunctionCall(GetToken(expr), e.Finite ? "Map#Build" : "IMap#Build", maptype, s, elt, elt2);
          }
          if (isLit) {
            // Lit-lifting: All keys and values are lit, so the map is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          return e.MemberSelectCase(
            field => {
              var useSurrogateLocal = translator.inBodyInitContext && Expression.AsThis(e.Obj) != null && !field.IsInstanceIndependentConstant;
              if (useSurrogateLocal) {
                return new Boogie.IdentifierExpr(GetToken(expr), translator.SurrogateName(field), translator.TrType(field.Type));
              } else if (field is ConstantField) {
                var typeMap = e.TypeArgumentSubstitutionsWithParents();
                var args = GetTypeParams(field.EnclosingClass).ConvertAll(tp => translator.TypeToTy(typeMap[tp]));
                Boogie.Expr result;
                if (field.IsStatic) {
                  result = new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(translator.GetReadonlyField(field)), args);
                } else {
                  Boogie.Expr obj = TrExpr(e.Obj);
                  args.Add(obj);
                  result = new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(translator.GetReadonlyField(field)), args);
                }
                result = translator.CondApplyUnbox(GetToken(expr), result, field.Type, expr.Type);
                return result;
              } else {
                Boogie.Expr obj = TrExpr(e.Obj);
                Boogie.Expr result;
                if (field.IsMutable) {
                  result = ReadHeap(GetToken(expr), HeapExpr, obj, new Boogie.IdentifierExpr(GetToken(expr), translator.GetField(field)));
                  return translator.CondApplyUnbox(GetToken(expr), result, field.Type, expr.Type);
                } else {
                  result = new Boogie.NAryExpr(GetToken(expr), new Boogie.FunctionCall(translator.GetReadonlyField(field)),
                    new List<Boogie.Expr> { obj });
                  result = translator.CondApplyUnbox(GetToken(expr), result, field.Type, expr.Type);
                  if (translator.IsLit(obj)) {
                    result = MaybeLit(result, translator.TrType(expr.Type));
                  }
                  return result;
                }
              }
            },
            fn => {
              var typeMap = e.TypeArgumentSubstitutionsWithParents();
              var args = GetTypeParams(fn).ConvertAll(tp => translator.TypeToTy(typeMap[tp]));
              if (fn.IsFuelAware()) {
                args.Add(this.layerInterCluster.GetFunctionFuel(fn));
              }
              if (fn is TwoStateFunction) {
                args.Add(Old.HeapExpr);
              }
              if (!fn.IsStatic) {
                args.Add(/* translator.BoxIfUnboxed */(TrExpr(e.Obj)/*, e.Type */));
              }
              return FunctionCall(GetToken(e), translator.FunctionHandle(fn), predef.HandleType, args);
            });
        } else if (expr is SeqSelectExpr) {
          SeqSelectExpr e = (SeqSelectExpr)expr;
          Boogie.Expr seq = TrExpr(e.Seq);
          var seqType = e.Seq.Type.NormalizeExpand();
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
          Boogie.Type elType = translator.TrType(elmtType);
          Boogie.Type dType = translator.TrType(domainType);
          Boogie.Expr e0 = e.E0 == null ? null : TrExpr(e.E0);
          if (e0 != null && e.E0.Type.IsBitVectorType) {
            e0 = translator.ConvertExpression(GetToken(e.E0), e0, e.E0.Type, Type.Int);
          }
          Boogie.Expr e1 = e.E1 == null ? null : TrExpr(e.E1);
          if (e1 != null && e.E1.Type.IsBitVectorType) {
            e1 = translator.ConvertExpression(GetToken(e.E1), e1, e.E1.Type, Type.Int);
          }
          if (e.SelectOne) {
            Contract.Assert(e1 == null);
            Boogie.Expr x;
            if (seqType.IsArrayType) {
              Boogie.Expr fieldName = translator.FunctionCall(GetToken(expr), BuiltinFunction.IndexField, null, e0);
              x = ReadHeap(GetToken(expr), HeapExpr, TrExpr(e.Seq), fieldName);
            } else if (seqType is SeqType) {
              x = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqIndex, predef.BoxType, seq, e0);
            } else if (seqType is MapType) {
              bool finite = ((MapType)seqType).Finite;
              var f = finite ? BuiltinFunction.MapElements : BuiltinFunction.IMapElements;
              x = translator.FunctionCall(GetToken(expr), f, predef.MapType(GetToken(e), finite, predef.BoxType, predef.BoxType), seq);
              x = Boogie.Expr.Select(x, BoxIfNecessary(GetToken(e), e0, domainType));
            } else if (seqType is MultiSetType) {
              x = Boogie.Expr.SelectTok(GetToken(expr), TrExpr(e.Seq), BoxIfNecessary(GetToken(expr), e0, domainType));
            } else { Contract.Assert(false); x = null; }
            if (!ModeledAsBoxType(elmtType) && !(seqType is MultiSetType)) {
              x = translator.FunctionCall(GetToken(expr), BuiltinFunction.Unbox, elType, x);
            }
            return x;
          } else {
            if (seqType.IsArrayType) {
              seq = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqFromArray, elType, HeapExpr, seq);
            }
            var isLit = translator.IsLit(seq);
            if (e1 != null) {
              isLit = isLit && translator.IsLit(e1);
              seq = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqTake, elType, seq, e1);
            }
            if (e0 != null) {
              isLit = isLit && translator.IsLit(e0);
              seq = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqDrop, elType, seq, e0);
            }
            // if e0 == null && e1 == null, then we have the identity operation seq[..] == seq;
            if (isLit && (e0 != null || e1 != null)) {
              // Lit-lift the expression
              seq = MaybeLit(seq, translator.TrType(expr.Type));
            }
            return seq;
          }

        } else if (expr is SeqUpdateExpr) {
          SeqUpdateExpr e = (SeqUpdateExpr)expr;
          Boogie.Expr seq = TrExpr(e.Seq);
          var seqType = e.Seq.Type.NormalizeExpand();
          if (seqType is SeqType) {
            Type elmtType = cce.NonNull((SeqType)seqType).Arg;
            Boogie.Expr index = TrExpr(e.Index);
            index = translator.ConvertExpression(GetToken(e.Index), index, e.Index.Type, Type.Int);
            Boogie.Expr val = BoxIfNecessary(GetToken(expr), TrExpr(e.Value), elmtType);
            return translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqUpdate, predef.BoxType, seq, index, val);
          } else if (seqType is MapType) {
            MapType mt = (MapType)seqType;
            Boogie.Type maptype = predef.MapType(GetToken(expr), mt.Finite, predef.BoxType, predef.BoxType);
            Boogie.Expr index = BoxIfNecessary(GetToken(expr), TrExpr(e.Index), mt.Domain);
            Boogie.Expr val = BoxIfNecessary(GetToken(expr), TrExpr(e.Value), mt.Range);
            return FunctionCall(GetToken(expr), mt.Finite ? "Map#Build" : "IMap#Build", maptype, seq, index, val);
          } else if (seqType is MultiSetType) {
            Type elmtType = cce.NonNull((MultiSetType)seqType).Arg;
            Boogie.Expr index = BoxIfNecessary(GetToken(expr), TrExpr(e.Index), elmtType);
            Boogie.Expr val = TrExpr(e.Value);
            return Boogie.Expr.StoreTok(GetToken(expr), seq, index, val);
          } else {
            Contract.Assert(false);
            throw new cce.UnreachableException();
          }
        } else if (expr is MultiSelectExpr) {
          MultiSelectExpr e = (MultiSelectExpr)expr;
          Type elmtType = UserDefinedType.ArrayElementType(e.Array.Type); ;
          Boogie.Type elType = translator.TrType(elmtType);

          Boogie.Expr fieldName = GetArrayIndexFieldName(GetToken(expr), e.Indices);
          Boogie.Expr x = ReadHeap(GetToken(expr), HeapExpr, TrExpr(e.Array), fieldName);
          if (!ModeledAsBoxType(elmtType)) {
            x = translator.FunctionCall(GetToken(expr), BuiltinFunction.Unbox, elType, x);
          }
          return x;

        } else if (expr is ApplyExpr) {
          ApplyExpr e = (ApplyExpr)expr;
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
              return TrExpr(new FunctionCallExpr(e.tok, fn.Name, mem.Obj, e.tok, e.CloseParen, e.Args) {
                Function = fn,
                Type = e.Type,
                TypeApplication_AtEnclosingClass = mem.TypeApplication_AtEnclosingClass,
                TypeApplication_JustFunction = mem.TypeApplication_JustMember
              });
            }
          }

          Func<Expression, Boogie.Expr> TrArg = arg => translator.BoxIfUnboxed(TrExpr(arg), arg.Type);

          var applied = FunctionCall(GetToken(expr), Translator.Apply(arity), predef.BoxType,
            Concat(Map(tt.TypeArgs, translator.TypeToTy),
              Cons(HeapExpr, Cons(TrExpr(e.Function), e.Args.ConvertAll(arg => TrArg(arg))))));

          return translator.UnboxIfBoxed(applied, tt.Result);

        } else if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          if (e.Function is SpecialFunction) {
            return TrExprSpecialFunctionCall(e);
          } else {
            Boogie.Expr layerArgument;
            var etran = this;
            if (e.Function.ContainsQuantifier && translator.stmtContext == StmtType.ASSUME && translator.adjustFuelForExists) {
              // we need to increase fuel functions that contain quantifier expr in the assume context.
              etran = etran.LayerOffset(1);
              translator.adjustFuelForExists = false;
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

            var ty = translator.TrType(e.Type);
            var id = new Boogie.IdentifierExpr(GetToken(e), e.Function.FullSanitizedName, ty);

            bool argsAreLit;
            var args = FunctionInvocationArguments(e, layerArgument, false, out argsAreLit);
            Expr result = new Boogie.NAryExpr(GetToken(e), new Boogie.FunctionCall(id), args);
            result = translator.CondApplyUnbox(GetToken(e), result, e.Function.ResultType, e.Type);

            bool callIsLit = argsAreLit
                             && Translator.FunctionBodyIsAvailable(e.Function, translator.currentModule, translator.currentScope, true)
                             && !e.Function.Reads.Any(); // Function could depend on external values
            if (callIsLit) {
              result = MaybeLit(result, ty);
            }

            return result;
          }
        } else if (expr is DatatypeValue) {
          DatatypeValue dtv = (DatatypeValue)expr;
          Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
          List<Boogie.Expr> args = new List<Boogie.Expr>();

          bool argsAreLit = true;
          for (int i = 0; i < dtv.Arguments.Count; i++) {
            Expression arg = dtv.Arguments[i];
            Type t = dtv.Ctor.Formals[i].Type;
            var bArg = TrExpr(arg);
            argsAreLit = argsAreLit && translator.IsLit(bArg);
            args.Add(translator.CondApplyBox(GetToken(expr), bArg, cce.NonNull(arg.Type), t));
          }
          Boogie.IdentifierExpr id = new Boogie.IdentifierExpr(GetToken(dtv), dtv.Ctor.FullName, predef.DatatypeType);
          Boogie.Expr ret = new Boogie.NAryExpr(GetToken(dtv), new Boogie.FunctionCall(id), args);
          if (argsAreLit) {
            // If all arguments are Lit, so is the whole expression
            ret = MaybeLit(ret, predef.DatatypeType);
          }
          return ret;

        } else if (expr is SeqConstructionExpr) {
          var e = (SeqConstructionExpr)expr;
          var eType = e.Type.AsSeqType.Arg.NormalizeExpand();
          return FunctionCall(GetToken(expr), "Seq#Create", predef.SeqType(GetToken(e), predef.BoxType), translator.TypeToTy(eType), HeapExpr, TrExpr(e.N), TrExpr(e.Initializer));

        } else if (expr is MultiSetFormingExpr) {
          MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
          var eType = e.E.Type.NormalizeExpand();
          if (eType is SetType) {
            return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetFromSet, translator.TrType(cce.NonNull((SetType)eType).Arg), TrExpr(e.E));
          } else if (eType is SeqType) {
            return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetFromSeq, translator.TrType(cce.NonNull((SeqType)eType).Arg), TrExpr(e.E));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }

        } else if (expr is OldExpr) {
          var e = (OldExpr)expr;
          return OldAt(e.AtLabel).TrExpr(e.E);

        } else if (expr is UnchangedExpr) {
          var e = (UnchangedExpr)expr;
          return translator.FrameCondition(GetToken(e), e.Frame, false, FrameExpressionUse.Unchanged, OldAt(e.AtLabel), this, this, true);

        } else if (expr is UnaryOpExpr) {
          var e = (UnaryOpExpr)expr;
          Boogie.Expr arg = TrExpr(e.E);
          switch (e.ResolvedOp) {
            case UnaryOpExpr.ResolvedOpcode.Lit:
              return MaybeLit(arg);
            case UnaryOpExpr.ResolvedOpcode.BVNot:
              var bvWidth = expr.Type.AsBitVectorType.Width;
              var bvType = translator.BplBvType(bvWidth);
              Boogie.Expr r = FunctionCall(GetToken(expr), "not_bv" + bvWidth, bvType, arg);
              if (translator.IsLit(arg)) {
                r = MaybeLit(r, bvType);
              }
              return r;
            case UnaryOpExpr.ResolvedOpcode.BoolNot:
              return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, arg);
            case UnaryOpExpr.ResolvedOpcode.SeqLength:
              Contract.Assert(e.E.Type.NormalizeExpand() is SeqType);
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqLength, null, arg);
            case UnaryOpExpr.ResolvedOpcode.SetCard:
              Contract.Assert(e.E.Type.NormalizeExpand() is SetType { Finite: true });
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.SetCard, null, arg);
            case UnaryOpExpr.ResolvedOpcode.MultiSetCard:
              Contract.Assert(e.E.Type.NormalizeExpand() is MultiSetType);
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetCard, null, arg);
            case UnaryOpExpr.ResolvedOpcode.MapCard:
              Contract.Assert(e.E.Type.NormalizeExpand() is MapType { Finite: true });
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MapCard, null, arg);
            case UnaryOpExpr.ResolvedOpcode.Fresh:
              var freshLabel = ((FreshExpr)e).AtLabel;
              var eeType = e.E.Type.NormalizeExpand();
              if (eeType is SetType) {
                // generate:  (forall $o: ref :: { X[Box($o)] } X[Box($o)] ==> $o != null && !old($Heap)[$o,alloc])
                // OR, if X[Box($o)] is rewritten into smaller parts, use the less good trigger old($Heap)[$o,alloc]
                Boogie.Variable oVar = new Boogie.BoundVariable(GetToken(expr), new Boogie.TypedIdent(GetToken(expr), "$o", predef.RefType));
                Boogie.Expr o = new Boogie.IdentifierExpr(GetToken(expr), oVar);
                Boogie.Expr oNotNull = Boogie.Expr.Neq(o, predef.Null);
                bool performedInSetRewrite;
                Boogie.Expr oInSet = TrInSet(GetToken(expr), o, e.E, ((SetType)eeType).Arg, true, out performedInSetRewrite);
                Boogie.Expr oNotFresh = OldAt(freshLabel).IsAlloced(GetToken(expr), o);
                Boogie.Expr oIsFresh = Boogie.Expr.Not(oNotFresh);
                Boogie.Expr body = Boogie.Expr.Imp(oInSet, Boogie.Expr.And(oNotNull, oIsFresh));
                var trigger = BplTrigger(performedInSetRewrite ? oNotFresh : oInSet);
                return new Boogie.ForallExpr(GetToken(expr), new List<Variable> { oVar }, trigger, body);
              } else if (eeType is SeqType) {
                // generate:  (forall $i: int :: 0 <= $i && $i < Seq#Length(X) ==> Unbox(Seq#Index(X,$i)) != null && !old($Heap)[Unbox(Seq#Index(X,$i)),alloc])
                Boogie.Variable iVar = new Boogie.BoundVariable(GetToken(expr), new Boogie.TypedIdent(GetToken(expr), "$i", Boogie.Type.Int));
                Boogie.Expr i = new Boogie.IdentifierExpr(GetToken(expr), iVar);
                Boogie.Expr iBounds = translator.InSeqRange(GetToken(expr), i, Type.Int, TrExpr(e.E), true, null, false);
                Boogie.Expr XsubI = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqIndex, predef.RefType, TrExpr(e.E), i);
                XsubI = translator.FunctionCall(GetToken(expr), BuiltinFunction.Unbox, predef.RefType, XsubI);
                Boogie.Expr oNotFresh = OldAt(freshLabel).IsAlloced(GetToken(expr), XsubI);
                Boogie.Expr oIsFresh = Boogie.Expr.Not(oNotFresh);
                Boogie.Expr xsubiNotNull = Boogie.Expr.Neq(XsubI, predef.Null);
                Boogie.Expr body = Boogie.Expr.Imp(iBounds, Boogie.Expr.And(xsubiNotNull, oIsFresh));
                //TRIGGERS: Does this make sense? dafny0\SmallTests
                // BROKEN // NEW_TRIGGER
                //TRIG (forall $i: int :: 0 <= $i && $i < Seq#Length(Q#0) && $Unbox(Seq#Index(Q#0, $i)): ref != null ==> !read(old($Heap), $Unbox(Seq#Index(Q#0, $i)): ref, alloc))
                return new Boogie.ForallExpr(GetToken(expr), new List<Variable> { iVar }, body);
              } else {
                // generate:  x != null && !old($Heap)[x]
                Boogie.Expr oNull = Boogie.Expr.Neq(TrExpr(e.E), predef.Null);
                Boogie.Expr oIsFresh = Boogie.Expr.Not(OldAt(freshLabel).IsAlloced(GetToken(expr), TrExpr(e.E)));
                return Boogie.Expr.Binary(GetToken(expr), BinaryOperator.Opcode.And, oNull, oIsFresh);
              }
            case UnaryOpExpr.ResolvedOpcode.Allocated:
              // Translate with $IsAllocBox, even if it requires boxing the argument. This has the effect of giving
              // both the $IsAllocBox and $IsAlloc forms, because the axioms that connects these two is triggered
              // by $IsAllocBox.
              return translator.MkIsAllocBox(BoxIfNecessary(e.E.tok, TrExpr(e.E), e.E.Type), e.E.Type, HeapExpr);
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
          }

        } else if (expr is ConversionExpr) {
          var e = (ConversionExpr)expr;
          return translator.ConvertExpression(GetToken(e), TrExpr(e.E), e.E.Type, e.ToType);

        } else if (expr is TypeTestExpr) {
          var e = (TypeTestExpr)expr;
          return translator.GetSubrangeCheck(TrExpr(e.E), e.E.Type, e.ToType, out var _) ?? Boogie.Expr.True;

        } else if (expr is BinaryExpr) {
          BinaryExpr e = (BinaryExpr)expr;
          bool isReal = e.E0.Type.IsNumericBased(Type.NumericPersuasion.Real);
          int bvWidth = e.E0.Type.IsBitVectorType ? e.E0.Type.AsBitVectorType.Width : -1;  // -1 indicates "not a bitvector type"
          Boogie.Expr e0 = TrExpr(e.E0);
          if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet) {
            bool pr;
            return TrInSet(GetToken(expr), e0, e.E1, cce.NonNull(e.E0.Type), false, out pr);  // let TrInSet translate e.E1
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSet) {
            bool pr;
            Boogie.Expr arg = TrInSet(GetToken(expr), e0, e.E1, cce.NonNull(e.E0.Type), false, out pr);  // let TrInSet translate e.E1
            return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, arg);
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
            return TrInMultiSet(GetToken(expr), e0, e.E1, cce.NonNull(e.E0.Type), false); // let TrInMultiSet translate e.E1
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInMultiSet) {
            Boogie.Expr arg = TrInMultiSet(GetToken(expr), e0, e.E1, cce.NonNull(e.E0.Type), false);  // let TrInMultiSet translate e.E1
            return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, arg);
          }
          Boogie.Expr e1 = TrExpr(e.E1);
          BinaryOperator.Opcode bOpcode;
          Boogie.Type typ;
          var oe0 = e0;
          var oe1 = e1;
          var lit0 = Translator.GetLit(e0);
          var lit1 = Translator.GetLit(e1);
          bool liftLit = translator.IsLit(e0) && translator.IsLit(e1);
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
              var cot = e.E0.Type.AsCoDatatype;
              if (cot != null) {
                var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                return translator.CoEqualCall(cot, e0args, e1args, null, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, GetToken(expr));
              }
              if (e.E0.Type.IsIndDatatype) {
                return translator.TypeSpecificEqual(GetToken(expr), e.E0.Type, e0, e1);
              }
              typ = Boogie.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Eq; break;
            case BinaryExpr.ResolvedOpcode.NeqCommon:
              var cotx = e.E0.Type.AsCoDatatype;
              if (cotx != null) {
                var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                var eq = translator.CoEqualCall(cotx, e0args, e1args, null, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, GetToken(expr));
                return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, eq);
              }
              if (e.E0.Type.IsIndDatatype) {
                var eq = translator.TypeSpecificEqual(GetToken(expr), e.E0.Type, e0, e1);
                return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, eq);
              }
              typ = Boogie.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Neq; break;
            case BinaryExpr.ResolvedOpcode.Lt:
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "lt_bv" + bvWidth, Boogie.Type.Bool, e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return FunctionCall(GetToken(expr), "ORD#Less", Boogie.Type.Bool, e0, e1);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Boogie.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Lt;
                break;
              } else {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_lt_boogie", Boogie.Type.Bool, e0, e1, liftLit);
              }
            case BinaryExpr.ResolvedOpcode.LessThanLimit:
              return FunctionCall(GetToken(expr), "ORD#LessThanLimit", Boogie.Type.Bool, e0, e1);
            case BinaryExpr.ResolvedOpcode.Le:
              keepLits = true;
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "le_bv" + bvWidth, Boogie.Type.Bool, e0, e1, false);
              } else if (e.E0.Type.IsBigOrdinalType) {
                var less = FunctionCall(GetToken(expr), "ORD#Less", Boogie.Type.Bool, e0, e1);
                var eq = Boogie.Expr.Eq(e0, e1);
                return BplOr(eq, less);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Boogie.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Le;
                break;
              } else {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_le_boogie", Boogie.Type.Bool, e0, e1, false);
              }
            case BinaryExpr.ResolvedOpcode.Ge:
              keepLits = true;
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "ge_bv" + bvWidth, Boogie.Type.Bool, e0, e1, false);
              } else if (e.E0.Type.IsBigOrdinalType) {
                var less = FunctionCall(GetToken(expr), "ORD#Less", Boogie.Type.Bool, e1, e0);
                var eq = Boogie.Expr.Eq(e1, e0);
                return BplOr(eq, less);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Boogie.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Ge;
                break;
              } else {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_ge_boogie", Boogie.Type.Bool, e0, e1, false);
              }
            case BinaryExpr.ResolvedOpcode.Gt:
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "gt_bv" + bvWidth, Boogie.Type.Bool, e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return FunctionCall(GetToken(expr), "ORD#Less", Boogie.Type.Bool, e1, e0);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Boogie.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Gt;
                break;
              } else {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_gt_boogie", Boogie.Type.Bool, e0, e1, liftLit);
              }

            case BinaryExpr.ResolvedOpcode.Add:
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "add_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return TrToFunctionCall(GetToken(expr), "ORD#Plus", predef.BigOrdinalType, e0, e1, liftLit);
              } else if (e.E0.Type.IsCharType) {
                return TrToFunctionCall(GetToken(expr), "char#Plus", predef.CharType, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith) {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_add_boogie", Boogie.Type.Int, e0, e1, liftLit);
              } else if (!isReal && (DafnyOptions.O.ArithMode == 2 || 5 <= DafnyOptions.O.ArithMode)) {
                return TrToFunctionCall(GetToken(expr), "Add", Boogie.Type.Int, oe0, oe1, liftLit);
              } else {
                typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                bOpcode = BinaryOperator.Opcode.Add;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Sub:
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "sub_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return TrToFunctionCall(GetToken(expr), "ORD#Minus", predef.BigOrdinalType, e0, e1, liftLit);
              } else if (e.E0.Type.IsCharType) {
                return TrToFunctionCall(GetToken(expr), "char#Minus", predef.CharType, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith) {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_sub_boogie", Boogie.Type.Int, e0, e1, liftLit);
              } else if (!isReal && (DafnyOptions.O.ArithMode == 2 || 5 <= DafnyOptions.O.ArithMode)) {
                return TrToFunctionCall(GetToken(expr), "Sub", Boogie.Type.Int, oe0, oe1, liftLit);
              } else {
                typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                bOpcode = BinaryOperator.Opcode.Sub;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Mul:
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "mul_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith) {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_mul_boogie", Boogie.Type.Int, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3) {
                return TrToFunctionCall(GetToken(expr), "Mul", Boogie.Type.Int, oe0, oe1, liftLit);
              } else {
                typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                bOpcode = BinaryOperator.Opcode.Mul;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Div:
              if (0 <= bvWidth) {
                return TrToFunctionCall(GetToken(expr), "div_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith && !isReal) {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_div_boogie", Boogie.Type.Int, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3) {
                return TrToFunctionCall(GetToken(expr), "Div", Boogie.Type.Int, e0, oe1, liftLit);
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
                return TrToFunctionCall(GetToken(expr), "mod_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (DafnyOptions.O.DisableNLarith && !isReal) {
                return TrToFunctionCall(GetToken(expr), "INTERNAL_mod_boogie", Boogie.Type.Int, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3) {
                return TrToFunctionCall(GetToken(expr), "Mod", Boogie.Type.Int, e0, oe1, liftLit);
              } else {
                typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
                bOpcode = BinaryOperator.Opcode.Mod;
                break;
              }

            case BinaryExpr.ResolvedOpcode.LeftShift: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(GetToken(expr), "LeftShift_bv" + bvWidth, translator.BplBvType(bvWidth), e0, translator.ConvertExpression(GetToken(expr), e1, e.E1.Type, e.Type), liftLit);
              }
            case BinaryExpr.ResolvedOpcode.RightShift: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(GetToken(expr), "RightShift_bv" + bvWidth, translator.BplBvType(bvWidth), e0, translator.ConvertExpression(GetToken(expr), e1, e.E1.Type, e.Type), liftLit);
              }
            case BinaryExpr.ResolvedOpcode.BitwiseAnd: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(GetToken(expr), "and_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              }
            case BinaryExpr.ResolvedOpcode.BitwiseOr: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(GetToken(expr), "or_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              }
            case BinaryExpr.ResolvedOpcode.BitwiseXor: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(GetToken(expr), "xor_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              }

            case BinaryExpr.ResolvedOpcode.LtChar:
            case BinaryExpr.ResolvedOpcode.LeChar:
            case BinaryExpr.ResolvedOpcode.GeChar:
            case BinaryExpr.ResolvedOpcode.GtChar: {
                // work off the original operands (that is, allow them to be lit-wrapped)
                var operand0 = translator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe0);
                var operand1 = translator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe1);
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
                return Boogie.Expr.Binary(GetToken(expr), bOp, operand0, operand1);
              }

            case BinaryExpr.ResolvedOpcode.SetEq:
            case BinaryExpr.ResolvedOpcode.MultiSetEq:
            case BinaryExpr.ResolvedOpcode.SeqEq:
            case BinaryExpr.ResolvedOpcode.MapEq:
              return translator.TypeSpecificEqual(GetToken(expr), e.E0.Type, e0, e1);
            case BinaryExpr.ResolvedOpcode.SetNeq:
            case BinaryExpr.ResolvedOpcode.MultiSetNeq:
            case BinaryExpr.ResolvedOpcode.SeqNeq:
            case BinaryExpr.ResolvedOpcode.MapNeq:
              return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, translator.TypeSpecificEqual(GetToken(expr), e.E0.Type, e0, e1));

            case BinaryExpr.ResolvedOpcode.ProperSubset: {
                return translator.ProperSubset(GetToken(expr), e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.Subset: {
                bool finite = e.E1.Type.AsSetType.Finite;
                var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
                return translator.FunctionCall(GetToken(expr), f, null, e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.Superset: {
                bool finite = e.E1.Type.AsSetType.Finite;
                var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
                return translator.FunctionCall(GetToken(expr), f, null, e1, e0);
              }
            case BinaryExpr.ResolvedOpcode.ProperSuperset:
              return translator.ProperSubset(GetToken(expr), e1, e0);
            case BinaryExpr.ResolvedOpcode.Disjoint: {
                bool finite = e.E1.Type.AsSetType.Finite;
                var f = finite ? BuiltinFunction.SetDisjoint : BuiltinFunction.ISetDisjoint;
                return translator.FunctionCall(GetToken(expr), f, null, e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.InSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.Union: {
                bool finite = e.E1.Type.AsSetType.Finite;
                var f = finite ? BuiltinFunction.SetUnion : BuiltinFunction.ISetUnion;
                return translator.FunctionCall(GetToken(expr), f, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.Intersection: {
                bool finite = e.E1.Type.AsSetType.Finite;
                var f = finite ? BuiltinFunction.SetIntersection : BuiltinFunction.ISetIntersection;
                return translator.FunctionCall(GetToken(expr), f, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.SetDifference: {
                bool finite = e.E1.Type.AsSetType.Finite;
                var f = finite ? BuiltinFunction.SetDifference : BuiltinFunction.ISetDifference;
                return translator.FunctionCall(GetToken(expr), f, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
              return translator.ProperMultiset(GetToken(expr), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSubset:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetSubset, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSuperset:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetSubset, null, e1, e0);
            case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
              return translator.ProperMultiset(GetToken(expr), e1, e0);
            case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetDisjoint, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.InMultiSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInMultiSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetUnion, translator.TrType(expr.Type.AsMultiSetType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetIntersection, translator.TrType(expr.Type.AsMultiSetType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetDifference:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.MultiSetDifference, translator.TrType(expr.Type.AsMultiSetType.Arg), e0, e1);

            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              return translator.ProperPrefix(GetToken(expr), e0, e1);
            case BinaryExpr.ResolvedOpcode.Prefix: {
                Boogie.Expr len0 = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqLength, null, e0);
                Boogie.Expr len1 = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqLength, null, e1);
                return Boogie.Expr.Binary(GetToken(expr), BinaryOperator.Opcode.And,
                  Boogie.Expr.Le(len0, len1),
                  translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
              }
            case BinaryExpr.ResolvedOpcode.Concat:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqAppend, translator.TrType(expr.Type.AsSeqType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.InSeq:
              return translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqContains, null, e1,
                BoxIfNecessary(GetToken(expr), e0, cce.NonNull(e.E0.Type)));
            case BinaryExpr.ResolvedOpcode.NotInSeq:
              Boogie.Expr arg = translator.FunctionCall(GetToken(expr), BuiltinFunction.SeqContains, null, e1,
                BoxIfNecessary(GetToken(expr), e0, cce.NonNull(e.E0.Type)));
              return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, arg);
            case BinaryExpr.ResolvedOpcode.InMap: {
                bool finite = e.E1.Type.AsMapType.Finite;
                var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
                return Boogie.Expr.SelectTok(GetToken(expr), translator.FunctionCall(GetToken(expr), f, predef.MapType(GetToken(e), finite, predef.BoxType, predef.BoxType), e1),
                  BoxIfNecessary(GetToken(expr), e0, e.E0.Type));
              }
            case BinaryExpr.ResolvedOpcode.NotInMap: {
                bool finite = e.E1.Type.AsMapType.Finite;
                var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
                Boogie.Expr inMap = Boogie.Expr.SelectTok(GetToken(expr), translator.FunctionCall(GetToken(expr), f, predef.MapType(GetToken(e), finite, predef.BoxType, predef.BoxType), e1),
                  BoxIfNecessary(GetToken(expr), e0, e.E0.Type));
                return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, inMap);
              }
            case BinaryExpr.ResolvedOpcode.MapMerge: {
                bool finite = e.E0.Type.AsMapType.Finite;
                var f = finite ? "Map#Merge" : "IMap#Merge";
                return FunctionCall(GetToken(expr), f, translator.TrType(expr.Type), e0, e1);
              }
            case BinaryExpr.ResolvedOpcode.MapSubtraction: {
                bool finite = e.E0.Type.AsMapType.Finite;
                var f = finite ? "Map#Subtract" : "IMap#Subtract";
                return FunctionCall(GetToken(expr), f, translator.TrType(expr.Type), e0, e1);
              }

            case BinaryExpr.ResolvedOpcode.RankLt:
              return Boogie.Expr.Binary(GetToken(expr), BinaryOperator.Opcode.Lt,
                translator.FunctionCall(GetToken(expr), e.E0.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e0),
                translator.FunctionCall(GetToken(expr), BuiltinFunction.DtRank, null, e1));
            case BinaryExpr.ResolvedOpcode.RankGt:
              return Boogie.Expr.Binary(GetToken(expr), BinaryOperator.Opcode.Gt,
                translator.FunctionCall(GetToken(expr), BuiltinFunction.DtRank, null, e0),
                translator.FunctionCall(GetToken(expr), e.E1.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e1));

            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
          }
          liftLit = liftLit && !keepLits;
          var ae0 = keepLits ? oe0 : e0;
          var ae1 = keepLits ? oe1 : e1;
          Boogie.Expr re = Boogie.Expr.Binary(GetToken(expr), bOpcode, ae0, ae1);
          if (liftLit) {
            re = MaybeLit(re, typ);
          }
          return re;
        } else if (expr is TernaryExpr) {
          var e = (TernaryExpr)expr;
          var e0 = TrExpr(e.E0);
          if (!TernaryExpr.PrefixEqUsesNat && !e.E0.Type.IsBigOrdinalType) {
            e0 = FunctionCall(e0.tok, "ORD#FromNat", predef.BigOrdinalType, e0);
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
              var r = translator.CoEqualCall(cot, e1type.TypeArgs, e2type.TypeArgs, e0, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e1, e2);
              if (e.Op == TernaryExpr.Opcode.PrefixEqOp) {
                return r;
              } else {
                return Boogie.Expr.Unary(GetToken(expr), UnaryOperator.Opcode.Not, r);
              }
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected ternary expression
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          if (!e.Exact) {
            var d = translator.LetDesugaring(e);
            return TrExpr(d);
          } else {
            List<Boogie.Variable> lhss;
            List<Boogie.Expr> rhss;
            TrLetExprPieces(e, out lhss, out rhss);
            // in the translation of body, treat a let-bound variable as IsLit if its RHS definition is IsLit
            Contract.Assert(lhss.Count == rhss.Count);  // this is a postcondition of TrLetExprPieces
            var previousCount = translator.letBoundVariablesWithLitRHS.Count;
            for (var i = 0; i < lhss.Count; i++) {
              if (translator.IsLit(rhss[i])) {
                translator.letBoundVariablesWithLitRHS.Add(lhss[i].Name);
              }
              i++;
            }
            var body = TrExpr(e.Body);
            foreach (var v in lhss) {
              translator.letBoundVariablesWithLitRHS.Remove(v.Name);
            }
            Contract.Assert(previousCount == translator.letBoundVariablesWithLitRHS.Count);
            // in the following, use the token for Body instead of the token for the whole let expression; this gives better error locations
            return new Boogie.LetExpr(GetToken(e.Body), lhss, rhss, null, body);
          }
        } else if (expr is QuantifierExpr) {
          QuantifierExpr e = (QuantifierExpr)expr;

          if (e.SplitQuantifier != null) {
            return TrExpr(e.SplitQuantifierExpression);
          } else {
            List<Variable> bvars = new List<Variable>();
            var bodyEtran = this;
            if (e is ExistsExpr && translator.stmtContext == StmtType.ASSERT && translator.adjustFuelForExists) {
              // assert exists need decrease fuel by 1
              bodyEtran = bodyEtran.DecreaseFuel(1);
              // set adjustFuelForExists to false so that we don't keep decrease the fuel in cases like the expr below.
              // assert exists p:int :: exists t:T :: ToInt(t) > 0;
              translator.adjustFuelForExists = false;
            } else if (e is ExistsExpr && translator.stmtContext == StmtType.ASSUME && translator.adjustFuelForExists) {
              // assume exists need increase fuel by 1
              bodyEtran = bodyEtran.LayerOffset(1);
              translator.adjustFuelForExists = false;
            }

            Boogie.Expr antecedent = Boogie.Expr.True;

            List<bool> freeOfAlloc = null;
            if (FrugalHeapUseX) {
              freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
            }
            antecedent = BplAnd(antecedent, bodyEtran.TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc)); // initHeapForAllStmt

            Boogie.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
            Boogie.Trigger tr = translator.TrTrigger(bodyEtran, e.Attributes, GetToken(e), bvars, null, null);

            if (e.Range != null) {
              antecedent = BplAnd(antecedent, bodyEtran.TrExpr(e.Range));
            }
            Boogie.Expr body = bodyEtran.TrExpr(e.Term);

            if (e is ForallExpr) {
              return new Boogie.ForallExpr(GetToken(expr), new List<TypeVariable>(), bvars, kv, tr, Boogie.Expr.Imp(antecedent, body));
            } else {
              Contract.Assert(e is ExistsExpr);
              return new Boogie.ExistsExpr(GetToken(expr), new List<TypeVariable>(), bvars, kv, tr, Boogie.Expr.And(antecedent, body));
            }
          }
        } else if (expr is SetComprehension) {
          var e = (SetComprehension)expr;
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          // Translate "set xs | R :: T" into:
          //     lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))
          // or if "T" is "xs", then:
          //     lambda y: BoxType :: CorrectType(y) && R[xs := Unbox(y)]
          var yVar = new Boogie.BoundVariable(GetToken(expr), new Boogie.TypedIdent(GetToken(expr), translator.CurrentIdGenerator.FreshId("$y#"), predef.BoxType));
          Boogie.Expr y = new Boogie.IdentifierExpr(GetToken(expr), yVar);
          Boogie.Expr lbody;
          if (e.TermIsSimple) {
            var bv = e.BoundVars[0];
            // lambda y: BoxType :: CorrectType(y) && R[xs := yUnboxed]
            Boogie.Expr typeAntecedent = translator.MkIsBox(new Boogie.IdentifierExpr(GetToken(expr), yVar), bv.Type);
            if (freeOfAlloc != null && !freeOfAlloc[0]) {
              var isAlloc = translator.MkIsAllocBox(new Boogie.IdentifierExpr(GetToken(expr), yVar), bv.Type, HeapExpr);
              typeAntecedent = BplAnd(typeAntecedent, isAlloc);
            }
            var yUnboxed = translator.UnboxIfBoxed(new Boogie.IdentifierExpr(GetToken(expr), yVar), bv.Type);
            var range = Translator.Substitute(e.Range, bv, new BoogieWrapper(yUnboxed, bv.Type));
            lbody = BplAnd(typeAntecedent, TrExpr(range));
          } else {
            // lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))
            List<Variable> bvars = new List<Variable>();
            Boogie.Expr typeAntecedent = TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc);

            var eq = Boogie.Expr.Eq(y, BoxIfNecessary(GetToken(expr), TrExpr(e.Term), e.Term.Type));
            var ebody = Boogie.Expr.And(BplAnd(typeAntecedent, TrExpr(e.Range)), eq);
            var triggers = translator.TrTrigger(this, e.Attributes, GetToken(e));
            lbody = new Boogie.ExistsExpr(GetToken(expr), bvars, triggers, ebody);
          }
          Boogie.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
          return new Boogie.LambdaExpr(GetToken(expr), new List<TypeVariable>(), new List<Variable> { yVar }, kv, lbody);

        } else if (expr is MapComprehension) {
          var e = (MapComprehension)expr;
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
          List<Variable> bvars = new List<Variable>();
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }

          Boogie.QKeyValue kv = TrAttributes(e.Attributes, "trigger");

          var wVar = new Boogie.BoundVariable(GetToken(expr), new Boogie.TypedIdent(GetToken(expr), translator.CurrentIdGenerator.FreshId("$w#"), predef.BoxType));

          Boogie.Expr keys, values;
          if (!e.IsGeneralMapComprehension) {
            var bv = e.BoundVars[0];
            var w = new Boogie.IdentifierExpr(GetToken(expr), wVar);
            Boogie.Expr unboxw = translator.UnboxIfBoxed(w, bv.Type);
            Boogie.Expr typeAntecedent = translator.MkIsBox(w, bv.Type);
            if (freeOfAlloc != null && !freeOfAlloc[0]) {
              var isAlloc = translator.MkIsAllocBox(w, bv.Type, HeapExpr);
              typeAntecedent = BplAnd(typeAntecedent, isAlloc);
            }
            var subst = new Dictionary<IVariable, Expression>();
            subst.Add(bv, new BoogieWrapper(unboxw, bv.Type));

            var ebody = BplAnd(typeAntecedent, TrExpr(Translator.Substitute(e.Range, null, subst)));
            keys = new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), new List<Variable> { wVar }, kv, ebody);
            ebody = TrExpr(Translator.Substitute(e.Term, null, subst));
            values = new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), new List<Variable> { wVar }, kv, BoxIfNecessary(GetToken(expr), ebody, e.Term.Type));
          } else {
            var t = e.TermLeft;
            var w = new Boogie.IdentifierExpr(GetToken(expr), wVar);
            Boogie.Expr unboxw = translator.UnboxIfBoxed(w, t.Type);
            Boogie.Expr typeAntecedent = translator.MkIsBox(w, t.Type);
            if (freeOfAlloc != null && !freeOfAlloc[0]) {
              var isAlloc = translator.MkIsAllocBox(w, t.Type, HeapExpr);
              typeAntecedent = BplAnd(typeAntecedent, isAlloc);
            }
            List<Boogie.Variable> bvs;
            List<Boogie.Expr> args;
            translator.CreateBoundVariables(e.BoundVars, out bvs, out args);
            Contract.Assert(e.BoundVars.Count == bvs.Count);
            var subst = new Dictionary<IVariable, Expression>();
            for (var i = 0; i < e.BoundVars.Count; i++) {
              subst.Add(e.BoundVars[i], new BoogieWrapper(args[i], e.BoundVars[i].Type));
            }
            var rr = TrExpr(Translator.Substitute(e.Range, null, subst));
            var ff = TrExpr(Translator.Substitute(t, null, subst));
            var exst_body = BplAnd(rr, Boogie.Expr.Eq(unboxw, ff));
            var ebody = BplAnd(typeAntecedent, new Boogie.ExistsExpr(GetToken(e), bvs, exst_body));
            keys = new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), new List<Variable> { wVar }, kv, ebody);

            translator.CreateMapComprehensionProjectionFunctions(e);
            Contract.Assert(e.ProjectionFunctions != null && e.ProjectionFunctions.Count == e.BoundVars.Count);
            subst = new Dictionary<IVariable, Expression>();
            for (var i = 0; i < e.BoundVars.Count; i++) {
              var p = new Boogie.NAryExpr(GetToken(e), new Boogie.FunctionCall(e.ProjectionFunctions[i]), new List<Boogie.Expr> { unboxw });
              var prj = new BoogieWrapper(p, e.BoundVars[i].Type);
              subst.Add(e.BoundVars[i], prj);
            }
            ebody = TrExpr(Translator.Substitute(e.Term, null, subst));
            values = new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), new List<Variable> { wVar }, kv, BoxIfNecessary(GetToken(expr), ebody, e.Term.Type));
          }

          bool finite = e.Finite;
          var f = finite ? BuiltinFunction.MapGlue : BuiltinFunction.IMapGlue;
          return translator.FunctionCall(GetToken(e), f, null, keys, values, translator.TypeToTy(expr.Type));

        } else if (expr is LambdaExpr) {
          var e = (LambdaExpr)expr;
          return TrLambdaExpr(e);

        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          return TrExpr(e.E);

        } else if (expr is ITEExpr) {
          ITEExpr e = (ITEExpr)expr;
          var g = Translator.RemoveLit(TrExpr(e.Test));
          var thn = Translator.RemoveLit(TrExpr(e.Thn));
          var els = Translator.RemoveLit(TrExpr(e.Els));
          return new NAryExpr(GetToken(expr), new IfThenElse(GetToken(expr)), new List<Boogie.Expr> { g, thn, els });
        } else if (expr is MatchExpr) {
          var e = (MatchExpr)expr;
          var ite = DesugarMatchExpr(e);
          return TrExpr(ite);

        } else if (expr is ConcreteSyntaxExpression) {
          var e = (ConcreteSyntaxExpression)expr;
          return TrExpr(e.ResolvedExpression);

        } else if (expr is NestedMatchExpr nestedMatchExpr) {
          return TrExpr(nestedMatchExpr.Flattened);
        } else if (expr is BoxingCastExpr) {
          BoxingCastExpr e = (BoxingCastExpr)expr;
          return translator.CondApplyBox(GetToken(e), TrExpr(e.E), e.FromType, e.ToType);

        } else if (expr is UnboxingCastExpr) {
          UnboxingCastExpr e = (UnboxingCastExpr)expr;
          return translator.CondApplyUnbox(GetToken(e), TrExpr(e.E), e.FromType, e.ToType);

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
        }
      }

      public Expr TrExprSpecialFunctionCall(FunctionCallExpr expr) {
        Contract.Requires(expr.Function is SpecialFunction);
        string name = expr.Function.Name;
        if (name == "RotateLeft") {
          var w = expr.Type.AsBitVectorType.Width;
          Expression arg = expr.Args[0];
          return TrToFunctionCall(GetToken(expr), "LeftRotate_bv" + w, translator.BplBvType(w), TrExpr(expr.Receiver), translator.ConvertExpression(GetToken(expr), TrExpr(arg), arg.Type, expr.Type), false);
        } else if (name == "RotateRight") {
          var w = expr.Type.AsBitVectorType.Width;
          Expression arg = expr.Args[0];
          return TrToFunctionCall(GetToken(expr), "RightRotate_bv" + w, translator.BplBvType(w), TrExpr(expr.Receiver), translator.ConvertExpression(GetToken(expr), TrExpr(arg), arg.Type, expr.Type), false);
        } else {
          bool argsAreLit_dummy;
          var args = FunctionInvocationArguments(expr, null, true, out argsAreLit_dummy);
          var id = new Boogie.IdentifierExpr(GetToken(expr), expr.Function.FullSanitizedName, translator.TrType(expr.Type));
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

        var varNameGen = translator.CurrentIdGenerator.NestedFreshIdGenerator("$l#");

        var heap = BplBoundVar(varNameGen.FreshId("#heap#"), predef.HeapType, bvars);

        var ves = (from bv in e.BoundVars
                   select
BplBoundVar(varNameGen.FreshId(string.Format("#{0}#", bv.Name)), predef.BoxType, bvars)).ToList();
        var subst = e.BoundVars.Zip(ves, (bv, ve) => {
          var unboxy = translator.UnboxIfBoxed(ve, bv.Type);
          return new KeyValuePair<IVariable, Expression>(bv, new BoogieWrapper(unboxy, bv.Type));
        }).ToDictionary(x => x.Key, x => x.Value);
        var su = new Substituter(null, subst, new Dictionary<TypeParameter, Type>());

        var et = new ExpressionTranslator(this, heap);
        var lvars = new List<Boogie.Variable>();
        var ly = BplBoundVar(varNameGen.FreshId("#ly#"), predef.LayerType, lvars);
        et = et.WithLayer(ly);

        var ebody = et.TrExpr(Translator.Substitute(e.Body, null, subst));
        ebody = translator.BoxIfUnboxed(ebody, e.Body.Type);

        var isBoxes = BplAnd(ves.Zip(e.BoundVars, (ve, bv) => translator.MkIsBox(ve, bv.Type)));
        var reqbody = e.Range == null
          ? isBoxes
          : BplAnd(isBoxes, et.TrExpr(Translator.Substitute(e.Range, null, subst)));

        var rdvars = new List<Boogie.Variable>();
        var o = BplBoundVar(varNameGen.FreshId("#o#"), predef.RefType, rdvars);
        Boogie.Expr rdbody = new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), rdvars, null,
          translator.InRWClause(GetToken(e), o, null, e.Reads.ConvertAll(su.SubstFrameExpr), et, null, null));
        rdbody = FunctionCall(GetToken(e), "SetRef_to_SetBox", predef.SetType(GetToken(e), true, predef.BoxType), rdbody);

        return MaybeLit(
          translator.FunctionCall(GetToken(e), BuiltinFunction.AtLayer, predef.HandleType,
            new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), lvars, null,
              FunctionCall(GetToken(e), translator.Handle(e.BoundVars.Count), predef.BoxType,
                new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), bvars, null, ebody),
                new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), bvars, null, reqbody),
                new Boogie.LambdaExpr(GetToken(e), new List<TypeVariable>(), bvars, null, rdbody))),
            layerIntraCluster != null ? layerIntraCluster.ToExpr() : layerInterCluster.ToExpr()),
          predef.HandleType);
      }

      public void TrLetExprPieces(LetExpr let, out List<Boogie.Variable> lhss, out List<Boogie.Expr> rhss) {
        Contract.Requires(let != null);
        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < let.LHSs.Count; i++) {
          translator.AddCasePatternVarSubstitutions(let.LHSs[i], TrExpr(let.RHSs[i]), substMap);
        }
        lhss = new List<Boogie.Variable>();
        rhss = new List<Boogie.Expr>();
        foreach (var v in let.BoundVars) {
          var rhs = substMap[v];  // this should succeed (that is, "v" is in "substMap"), because the AddCasePatternVarSubstitutions calls above should have added a mapping for each bound variable in let.BoundVars
          Boogie.Expr bvIde;  // unused
          var bv = BplBoundVar(v.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(v.Type), out bvIde);
          lhss.Add(bv);
          rhss.Add(TrExpr(rhs));
        }
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
              var dv = new MemberSelectExpr(bv.tok, e.Source, dtor);
              substMap.Add(bv, dv);
            }
            argIndex++;
          }
          var c = Translator.Substitute(mc.Body, null, substMap);
          if (r == null) {
            r = c;
          } else {
            var test = new MemberSelectExpr(mc.tok, e.Source, mc.Ctor.QueryField);
            var ite = new ITEExpr(mc.tok, false, test, c, r);
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
          var tid = new Boogie.TypedIdent(bv.tok, bv.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(bv.Type));
          Boogie.Variable bvar;
          if (translateAsLocals) {
            bvar = new Boogie.LocalVariable(bv.tok, tid);
          } else {
            bvar = new Boogie.BoundVariable(bv.tok, tid);
          }
          bvars.Add(bvar);
          var useAlloc = freeOfAlloc == null || freeOfAlloc[i] ? NOALLOC : ISALLOC;
          Boogie.Expr wh = translator.GetWhereClause(bv.tok, new Boogie.IdentifierExpr(bv.tok, bvar), bv.Type, this, useAlloc);
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
          var tid = new Boogie.TypedIdent(bv.tok, bv.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(bv.Type));
          var bvar = new Boogie.BoundVariable(bv.tok, tid);
          var wh = translator.GetWhereClause(bv.tok, new Boogie.IdentifierExpr(bv.tok, bvar), bv.Type, this, NOALLOC);
          varsAndAntecedents.Add(Tuple.Create<Boogie.Variable, Boogie.Expr>(bvar, wh));
        }
        return varsAndAntecedents;
      }

      public Boogie.Expr TrBoundVariablesRename(List<BoundVar> boundVars, List<Variable> bvars, out Dictionary<IVariable, Expression> substMap, out Boogie.Trigger antitriggers) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);

        substMap = new Dictionary<IVariable, Expression>();
        antitriggers = null;
        Boogie.Expr typeAntecedent = Boogie.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var newBoundVar = new BoundVar(bv.tok, bv.Name, bv.Type);
          IdentifierExpr ie = new IdentifierExpr(newBoundVar.tok, newBoundVar.AssignUniqueName(translator.currentDeclaration.IdGenerator));
          ie.Var = newBoundVar; ie.Type = ie.Var.Type;  // resolve ie here
          substMap.Add(bv, ie);
          Boogie.Variable bvar = new Boogie.BoundVariable(newBoundVar.tok, new Boogie.TypedIdent(newBoundVar.tok, newBoundVar.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(newBoundVar.Type)));
          bvars.Add(bvar);
          var bIe = new Boogie.IdentifierExpr(bvar.tok, bvar);
          Boogie.Expr wh = translator.GetWhereClause(bv.tok, bIe, newBoundVar.Type, this, NOALLOC);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public List<Boogie.Expr> FunctionInvocationArguments(FunctionCallExpr e, Boogie.Expr layerArgument) {
        bool dummy;
        return FunctionInvocationArguments(e, layerArgument, false, out dummy);
      }

      public List<Boogie.Expr> FunctionInvocationArguments(FunctionCallExpr e, Boogie.Expr layerArgument, bool omitHeapArgument, out bool argsAreLit) {
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<List<Boogie.Expr>>() != null);

        var args = new List<Boogie.Expr>();

        // first add type arguments
        var tyParams = GetTypeParams(e.Function);
        var tySubst = e.TypeArgumentSubstitutionsWithParents();
        args.AddRange(translator.trTypeArgs(tySubst, tyParams));

        if (layerArgument != null) {
          args.Add(layerArgument);
        }
        if (e.Function is TwoStateFunction) {
          args.Add(OldAt(e.AtLabel).HeapExpr);
        }
        if (!omitHeapArgument && (AlwaysUseHeap || e.Function.ReadsHeap)) {
          Contract.Assert(HeapExpr != null);
          args.Add(HeapExpr);
          // If the function doesn't use the heap, but global settings say to use it,
          // then we want to quantify over the heap so that heap in the trigger can match over
          // heap modifying operations. (see Test/dafny4/Bug144.dfy)
          bool usesHeap = e.Function.ReadsHeap || e.Function.Formals.Any(f => f.Type.IsRefType);
          if (!usesHeap) {
            Statistics_HeapAsQuantifierCount++;
          }
        }
        argsAreLit = true;
        if (!e.Function.IsStatic) {
          var tr_ee = TrExpr(e.Receiver);
          argsAreLit = argsAreLit && translator.IsLit(tr_ee);
          args.Add(tr_ee);
        }
        for (int i = 0; i < e.Args.Count; i++) {
          Expression ee = e.Args[i];
          Type t = e.Function.Formals[i].Type;
          Expr tr_ee = TrExpr(ee);
          argsAreLit = argsAreLit && translator.IsLit(tr_ee);
          args.Add(translator.CondApplyBox(GetToken(e), tr_ee, cce.NonNull(ee.Type), t));
        }
        return args;
      }

      public Boogie.Expr GetArrayIndexFieldName(IToken tok, List<Expression> indices) {
        return translator.GetArrayIndexFieldName(tok, indices.ConvertAll(idx => {
          var e = TrExpr(idx);
          return translator.ConvertExpression(GetToken(idx), e, idx.Type, Type.Int);
        }));
      }

      public Boogie.Expr BoxIfNecessary(IToken tok, Boogie.Expr e, Type fromType) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(fromType != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);
        return translator.BoxIfNecessary(tok, e, fromType);
      }

      public static Boogie.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r, Expr f) {
        Contract.Requires(tok != null);
        Contract.Requires(heap != null);
        Contract.Requires(r != null);
        Contract.Requires(f != null);
        Contract.Ensures(Contract.Result<Boogie.NAryExpr>() != null);

        List<Boogie.Expr> args = new List<Boogie.Expr>();
        args.Add(heap);
        args.Add(r);
        args.Add(f);
        Boogie.Type t = (f.Type != null) ? f.Type : f.ShallowType;
        return new Boogie.NAryExpr(tok,
          new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, "read", t.AsCtor.Arguments[0])),
          args);
      }


      public static Boogie.NAryExpr UpdateHeap(IToken tok, Expr heap, Expr r, Expr f, Expr v) {
        Contract.Requires(tok != null);
        Contract.Requires(heap != null);
        Contract.Requires(r != null);
        Contract.Requires(f != null);
        Contract.Requires(v != null);
        Contract.Ensures(Contract.Result<Boogie.NAryExpr>() != null);

        List<Boogie.Expr> args = new List<Boogie.Expr>();
        args.Add(heap);
        args.Add(r);
        args.Add(f);
        args.Add(v);
        return new Boogie.NAryExpr(tok,
          new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, "update", heap.Type)),
          args);
      }

      /// <summary>
      /// Translate like s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// </summary>
      public Boogie.Expr TrInSet(IToken tok, Boogie.Expr elmt, Expression s, Type elmtType, bool aggressive, out bool performedRewrite) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
        var r = TrInSet_Aux(tok, elmt, elmtBox, s, aggressive, out performedRewrite);
        Contract.Assert(performedRewrite == RewriteInExpr(s, aggressive)); // sanity check
        return r;
      }
      /// <summary>
      /// The worker routine for TrInSet.  This method takes both "elmt" and "elmtBox" as parameters,
      /// using the former when the unboxed form is needed and the latter when the boxed form is needed.
      /// This gives the caller the flexibility to pass in either "o, Box(o)" or "Unbox(bx), bx".
      /// Note: This method must be kept in synch with RewriteInExpr.
      /// </summary>
      public Boogie.Expr TrInSet_Aux(IToken tok, Boogie.Expr elmt, Boogie.Expr elmtBox, Expression s, bool aggressive, out bool performedRewrite) {
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
              return Boogie.Expr.Or(TrInSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive, out pr), TrInSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive, out pr));
            case BinaryExpr.ResolvedOpcode.Intersection:
              return Boogie.Expr.And(TrInSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive, out pr), TrInSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive, out pr));
            case BinaryExpr.ResolvedOpcode.SetDifference:
              return Boogie.Expr.And(TrInSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive, out pr), Boogie.Expr.Not(TrInSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive, out pr)));
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
              disjunction = Boogie.Expr.Or(disjunction, disjunct);
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
            Boogie.Expr typeAntecedent = translator.GetWhereClause(GetToken(compr), elmt, compr.BoundVars[0].Type, this, NOALLOC) ?? Boogie.Expr.True;
            var range = Translator.Substitute(compr.Range, compr.BoundVars[0], new BoogieWrapper(elmt, compr.BoundVars[0].Type));
            return BplAnd(typeAntecedent, TrExpr(range));
          } else {
            // exists xs :: CorrectType(xs) && R && elmt==T
            List<bool> freeOfAlloc = null;
            if (FrugalHeapUseX) {
              freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(compr.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
            }
            var bvars = new List<Variable>();
            Boogie.Expr typeAntecedent = TrBoundVariables(compr.BoundVars, bvars, false, freeOfAlloc) ?? Boogie.Expr.True;
            var eq = Boogie.Expr.Eq(elmtBox, BoxIfNecessary(GetToken(compr), TrExpr(compr.Term), compr.Term.Type));
            var ebody = Boogie.Expr.And(BplAnd(typeAntecedent, TrExpr(compr.Range)), eq);
            var triggers = translator.TrTrigger(this, compr.Attributes, GetToken(compr));
            return new Boogie.ExistsExpr(GetToken(compr), bvars, triggers, ebody);
          }
        }
        performedRewrite = false;
        return Boogie.Expr.SelectTok(tok, TrExpr(s), elmtBox);
      }

      /// <summary>
      /// Translate like 0 < s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// Note: This method must be kept in synch with RewriteInExpr.
      /// </summary>
      public Boogie.Expr TrInMultiSet(IToken tok, Boogie.Expr elmt, Expression s, Type elmtType, bool aggressive) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);

        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);
        var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
        return TrInMultiSet_Aux(tok, elmt, elmtBox, s, aggressive);
      }
      public Boogie.Expr TrInMultiSet_Aux(IToken tok, Boogie.Expr elmt, Boogie.Expr elmtBox, Expression s, bool aggressive) {
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
              disjunction = Boogie.Expr.Or(disjunction, disjunct);
            }
          }
          if (disjunction == null) {
            return Boogie.Expr.False;
          } else {
            return disjunction;
          }
        }
        var result = Boogie.Expr.Gt(Boogie.Expr.SelectTok(tok, TrExpr(s), elmtBox), Boogie.Expr.Literal(0));
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

      public Boogie.QKeyValue TrAttributes(Attributes attrs, string skipThisAttribute) {
        Boogie.QKeyValue kv = null;
        bool hasNewTimeLimit = Attributes.Contains(attrs, "_timeLimit");
        bool hasNewRLimit = Attributes.Contains(attrs, "_rlimit");
        foreach (var attr in attrs.AsEnumerable()) {
          if (attr.Name == skipThisAttribute
              || attr.Name == "axiom"  // Dafny's axiom attribute clashes with Boogie's axiom keyword
              || attr.Name == "fuel"   // Fuel often uses function names as arguments, which adds extra axioms unnecessarily
              || (DafnyOptions.O.DisallowExterns && (attr.Name == "extern" || attr.Name == "dllimport")) // omit the extern attribute when /noExterns option is specified.
              || attr.Name == "timeLimitMultiplier"  // This is a Dafny-specific attribute
              || (attr.Name == "timeLimit" && hasNewTimeLimit)
              || (attr.Name == "rlimit" && hasNewRLimit)
          ) {
            continue;
          }
          List<object> parms = new List<object>();
          foreach (var arg in attr.Args) {
            var s = arg.AsStringLiteral();
            if (s != null) {
              // pass string literals down to Boogie as string literals, not as their expression translation
              parms.Add(s);
            } else {
              var e = TrExpr(arg);
              e = Translator.RemoveLit(e);
              parms.Add(e);
            }
          }

          var name = attr.Name;
          if (name == "_timeLimit") {
            name = "timeLimit";
          } else if (name == "_rlimit") {
            name = "rlimit";
          } else if (name == "synthesize") {
            name = "extern";
          }
          kv = new Boogie.QKeyValue(Token.NoToken, name, parms, kv);
        }
        return kv;
      }

      // --------------- help routines ---------------

      public Boogie.Expr IsAlloced(IToken tok, Boogie.Expr e) {
        Contract.Requires(HeapExpr != null);
        return translator.IsAlloced(tok, HeapExpr, e);
      }

      public Boogie.Expr GoodRef(IToken tok, Boogie.Expr e, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

        // Add $Is and $IsAlloc
        return translator.GetWhereClause(tok, e, type, this, ISALLOC);
      }
    }
  }
}
