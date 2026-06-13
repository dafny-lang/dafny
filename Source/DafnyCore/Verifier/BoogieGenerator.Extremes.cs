using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using System.Security.Cryptography;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Core;
using DafnyCore.Verifier;
using Microsoft.BaseTypes;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Triggers;
using Action = System.Action;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {


  /// <summary>
  /// In the following,
  /// if "pp" is a greatest predicate, then QQQ and NNN and HHH and EEE stand for "forall" and "" and "==>" and REVERSE-IMPLIES, and
  /// if "pp" is a least predicate, then QQQ and NNN and HHH and EEE stand for "exists" and "!" and "&&" and "==>".
  /// ==========  For co-predicates:
  /// Add the axioms:
  ///   forall args :: P(args) ==> QQQ k: nat :: P#[k](args)
  ///   forall args :: (QQQ k: nat :: P#[k](args)) ==> P(args)
  ///   forall args,k :: k == 0 ==> NNN P#[k](args)
  /// where "args" is "heap, formals".  In more details:
  ///   forall args :: { P(args) } args-have-appropriate-values && P(args) ==> QQQ k { P#[k](args) } :: 0 ATMOST k HHH P#[k](args)
  ///   forall args :: { P(args) } args-have-appropriate-values && (QQQ k :: 0 ATMOST k HHH P#[k](args)) ==> P(args)
  ///   forall args,k :: args-have-appropriate-values && k == 0 ==> NNN P#0#[k](args)
  ///   forall args,k,m :: args-have-appropriate-values && 0 ATMOST k LESS m ==> (P#[k](args) EEE P#[m](args))  (*)
  /// There is also a specialized version of (*) for least predicates.
  /// </summary>
  void AddPrefixPredicateAxioms(PrefixPredicate pp) {
    Contract.Requires(pp != null);
    Contract.Requires(Predef != null);
    var co = pp.ExtremePred;
    var tok = pp.Origin;
    var etran = new ExpressionTranslator(this, Predef, tok, pp);

    var tyvars = MkTyParamBinders(GetTypeParams(pp), out var tyexprs);

    var bvs = new List<Variable>(tyvars);
    var coArgs = new List<Bpl.Expr>(tyexprs);
    var prefixArgs = new List<Bpl.Expr>(tyexprs);
    var prefixArgsLimited = new List<Bpl.Expr>(tyexprs);
    var prefixArgsLimitedM = new List<Bpl.Expr>(tyexprs);
    if (pp.IsFuelAware()) {
      var sV = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$ly", Predef.LayerType));
      var s = new Bpl.IdentifierExpr(tok, sV);
      var succS = FunctionCall(tok, BuiltinFunction.LayerSucc, null, s);
      bvs.Add(sV);
      coArgs.Add(succS);
      prefixArgs.Add(succS);
      prefixArgsLimited.Add(s);
      prefixArgsLimitedM.Add(s);
    }

    Bpl.Expr h;
    if (pp.ReadsHeap) {
      var heapIdent = new Bpl.TypedIdent(tok, Predef.HeapVarName, Predef.HeapType);
      var bv = new Bpl.BoundVariable(tok, heapIdent);
      h = new Bpl.IdentifierExpr(tok, bv);
      bvs.Add(bv);
      coArgs.Add(h);
      prefixArgs.Add(h);
      prefixArgsLimited.Add(h);
      prefixArgsLimitedM.Add(h);
    } else {
      h = null;
    }

    // ante:  $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
    Bpl.Expr ante = h != null
      ? FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr)
      : (Bpl.Expr)Bpl.Expr.True;

    if (!pp.IsStatic) {
      var bvThis = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, etran.This, TrReceiverType(pp)));
      bvs.Add(bvThis);
      var bvThisIdExpr = new Bpl.IdentifierExpr(tok, bvThis);
      coArgs.Add(bvThisIdExpr);
      prefixArgs.Add(bvThisIdExpr);
      prefixArgsLimited.Add(bvThisIdExpr);
      prefixArgsLimitedM.Add(bvThisIdExpr);
      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(tok, pp);
      Bpl.Expr wh = BplAnd(
        ReceiverNotNull(bvThisIdExpr),
        GetWhereClause(tok, bvThisIdExpr, thisType, etran, NOALLOC));
      ante = BplAnd(ante, wh);
    }

    Bpl.Expr kWhere = null, kId = null, mId = null;
    Bpl.Variable k = null;
    Bpl.Variable m = null;

    // DR: Changed to add the pp formals instead of co (since types would otherwise be wrong)
    //     Note that k is not added to bvs or coArgs.
    foreach (var p in pp.Ins) {
      bool is_k = p == pp.Ins[0];
      var bv = new Bpl.BoundVariable(p.Origin,
        new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(pp.IdGenerator), TrType(p.Type)));
      var formal = new Bpl.IdentifierExpr(p.Origin, bv);
      if (!is_k) {
        coArgs.Add(formal);
      }

      prefixArgs.Add(formal);
      prefixArgsLimited.Add(formal);
      if (is_k) {
        m = new Bpl.BoundVariable(p.Origin, new Bpl.TypedIdent(p.Origin, "_m", TrType(p.Type)));
        mId = new Bpl.IdentifierExpr(m.tok, m);
        prefixArgsLimitedM.Add(mId);
      } else {
        prefixArgsLimitedM.Add(formal);
      }

      var wh = GetWhereClause(p.Origin, formal, p.Type, etran, NOALLOC);
      if (is_k) {
        // add the formal _k
        k = bv;
        kId = formal;
        kWhere = wh;
      } else {
        bvs.Add(bv);
        if (wh != null) {
          // add well-typedness conjunct to antecedent
          ante = BplAnd(ante, wh);
        }
      }
    }

    Contract.Assert(k != null && m != null); // the loop should have filled these in

    var funcID = new Bpl.IdentifierExpr(tok, co.FullSanitizedName, TrType(co.ResultType));
    var coAppl = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), coArgs);
    funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
    var prefixAppl = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgs);

    // forall args :: { P(args) } args-have-appropriate-values && P(args) ==> QQQ k { P#[k](args) } :: 0 ATMOST k HHH P#[k](args)
    var tr = BplTrigger(prefixAppl);
    var qqqK = pp.ExtremePred is GreatestPredicate
      ? (Bpl.Expr)new Bpl.ForallExpr(tok, [k], tr,
        kWhere == null ? prefixAppl : BplImp(kWhere, prefixAppl))
      : (Bpl.Expr)new Bpl.ExistsExpr(tok, [k], tr,
        kWhere == null ? prefixAppl : BplAnd(kWhere, prefixAppl));
    tr = BplTriggerHeap(this, tok, coAppl, pp.ReadsHeap ? null : h);
    var allS = new Bpl.ForallExpr(tok, bvs, tr, BplImp(BplAnd(ante, coAppl), qqqK));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, allS, "1st prefix predicate axiom for " + pp.FullSanitizedName));

    // forall args :: { P(args) } args-have-appropriate-values && (QQQ k :: 0 ATMOST k HHH P#[k](args)) ==> P(args)
    allS = new Bpl.ForallExpr(tok, bvs, tr, BplImp(BplAnd(ante, qqqK), coAppl));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, allS, "2nd prefix predicate axiom"));

    // forall args,k :: args-have-appropriate-values && k == 0 ==> NNN P#0#[k](args)
    var moreBvs = new List<Variable>();
    moreBvs.AddRange(bvs);
    moreBvs.Add(k);
    var z = Bpl.Expr.Eq(kId,
      pp.Ins[0].Type.IsBigOrdinalType
        ? (Bpl.Expr)FunctionCall(tok, "ORD#FromNat", Predef.BigOrdinalType, Bpl.Expr.Literal(0))
        : Bpl.Expr.Literal(0));
    funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
    Bpl.Expr prefixLimitedBody = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
    Bpl.Expr prefixLimited = pp.ExtremePred is LeastPredicate ? Bpl.Expr.Not(prefixLimitedBody) : prefixLimitedBody;

    var trigger = BplTriggerHeap(this, prefixLimitedBody.tok, prefixLimitedBody, pp.ReadsHeap ? null : h);
    var trueAtZero = new Bpl.ForallExpr(tok, moreBvs, trigger, BplImp(BplAnd(ante, z), prefixLimited));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, trueAtZero, "3rd prefix predicate axiom"));

#if WILLING_TO_TAKE_THE_PERFORMANCE_HIT
      // forall args,k,m :: args-have-appropriate-values && 0 <= k <= m ==> (P#[k](args) EEE P#[m](args))
      moreBvs = new List<Variable>();
      moreBvs.AddRange(bvs);
      moreBvs.Add(k);
      moreBvs.Add(m);
      Bpl.Expr smaller;
      if (kId.Type.IsInt) {
        smaller = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), kId), Bpl.Expr.Lt(kId, mId));
      } else {
        smaller = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, kId, mId);
      }
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      var prefixPred_K = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
      var prefixPred_M = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimitedM);
      var direction =
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      pp.ExtremePred is LeastPredicate ? BplImp(prefixPred_K, prefixPred_M) : BplImp(prefixPred_M, prefixPred_K);

      var trigger2 = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { prefixPred_K, prefixPred_M });
      var monotonicity = new Bpl.ForallExpr(tok, moreBvs, trigger2, BplImp(smaller, direction));
      AddRootAxiom(new Bpl.Axiom(tok, monotonicity, "prefix predicate monotonicity axiom"));
#endif
    // A more targeted monotonicity axiom used to increase the power of automation for proving the limit case for
    // least predicates that have more than one focal-predicate term.
    if (pp.ExtremePred is LeastPredicate && pp.Ins[0].Type.IsBigOrdinalType) {
      // forall args,k,m,limit ::
      //   { P#[k](args), ORD#LessThanLimit(k,limit), ORD#LessThanLimit(m,limit) }
      //   args-have-appropriate-values && k < m && P#[k](args) ==> P#[m](args))
      var limit = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "_limit", TrType(Type.BigOrdinal)));
      var limitId = new Bpl.IdentifierExpr(limit.tok, limit);
      moreBvs = [];
      moreBvs.AddRange(bvs);
      moreBvs.Add(k);
      moreBvs.Add(m);
      moreBvs.Add(limit);
      var kLessLimit = FunctionCall(tok, "ORD#LessThanLimit", Bpl.Type.Bool, kId, limitId);
      var mLessLimit = FunctionCall(tok, "ORD#LessThanLimit", Bpl.Type.Bool, mId, limitId);
      var kLessM = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, kId, mId);
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      var prefixPred_K = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
      var prefixPred_M = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimitedM);
      var direction = BplImp(prefixPred_K, prefixPred_M);

      var trigger3 = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { prefixPred_K, kLessLimit, mLessLimit });
      var monotonicity = new Bpl.ForallExpr(tok, moreBvs, trigger3, BplImp(kLessM, direction));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, monotonicity, "targeted prefix predicate monotonicity axiom"));
    }
  }

  /// <summary>
  /// For an extreme predicate P, "pp" is the prefix predicate for P (such that P = pp.ExtremePred) and
  /// "body" is the body of P.  Return what would be the body of the prefix predicate pp.
  /// In particular, return
  /// #if _k has type nat:
  ///   0 LESS _k  IMPLIES  body'                        // for greatest predicates
  ///   0 LESS _k  AND  body'                            // for least predicates
  /// #elsif _k has type ORDINAL:
  ///   (0 LESS ORD#Offset(_k)  IMPLIES  body') AND
  ///   (0 == ORD#Offset(_k) IMPLIES forall _k':ORDINAL :: _k' LESS _k ==> pp(_k', args))  // for greatest predicates
  ///   (0 == ORD#Offset(_k) IMPLIES exists _k':ORDINAL :: _k' LESS _k && pp(_k', args))   // for least predicates
  /// #endif
  /// where body' is body with the formals of P replaced by the corresponding
  /// formals of pp and with self-calls P(s) replaced by recursive calls to
  /// pp(_k - 1, s).
  /// </summary>
  Expression PrefixSubstitution(PrefixPredicate pp, Expression body) {
    Contract.Requires(pp != null);

    var typeMap = Util.Dict<TypeParameter, Type>(pp.ExtremePred.TypeArgs, Map(pp.TypeArgs, x => new UserDefinedType(x)));

    var paramMap = new Dictionary<IVariable, Expression>();
    for (int i = 0; i < pp.ExtremePred.Ins.Count; i++) {
      var replacement = pp.Ins[i + 1];  // the +1 is to skip pp's _k parameter
      var param = new IdentifierExpr(replacement.Origin, replacement.Name);
      param.Var = replacement;  // resolve here
      param.Type = replacement.Type;  // resolve here
      paramMap.Add(pp.ExtremePred.Ins[i], param);
    }

    var k = new IdentifierExpr(pp.Origin, pp.K.Name);
    k.Var = pp.K;  // resolve here
    k.Type = pp.K.Type;  // resolve here
    Expression kMinusOne = Expression.CreateSubtract(k, Expression.CreateNatLiteral(pp.Origin, 1, pp.K.Type));

    var s = new PrefixCallSubstituter(null, paramMap, typeMap, pp.ExtremePred, kMinusOne);
    body = s.Substitute(body);

    if (pp.K.Type.IsBigOrdinalType) {
      // 0 < k.Offset
      Contract.Assume(program.SystemModuleManager.ORDINAL_Offset != null);  // should have been filled in by the resolver
      var kOffset = new MemberSelectExpr(pp.Origin, k, program.SystemModuleManager.ORDINAL_Offset);
      var kIsPositive = Expression.CreateLess(Expression.CreateIntLiteral(pp.Origin, 0), kOffset);
      var kIsLimit = Expression.CreateEq(Expression.CreateIntLiteral(pp.Origin, 0), kOffset, Type.Int);
      var kprimeVar = new BoundVar(pp.Origin, "_k'", Type.BigOrdinal);
      var kprime = new IdentifierExpr(pp.Origin, kprimeVar);

      var substMap = new Dictionary<IVariable, Expression>();
      substMap.Add(pp.K, kprime);
      Expression recursiveCallReceiver;
      List<Expression> recursiveCallArgs;
      pp.RecursiveCallParameters(pp.Origin, pp.TypeArgs, pp.Ins, null, substMap, out recursiveCallReceiver, out recursiveCallArgs);
      var ppCall = new FunctionCallExpr(pp.Origin, pp.NameNode, recursiveCallReceiver, pp.Origin, Token.NoToken, recursiveCallArgs);
      ppCall.Function = pp;
      ppCall.Type = Type.Bool;
      ppCall.TypeApplication_AtEnclosingClass = pp.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      ppCall.TypeApplication_JustFunction = pp.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));

      Attributes triggerAttr = new Attributes("trigger", [ppCall], null);
      Expression limitCalls;
      if (pp.ExtremePred is GreatestPredicate) {
        // forall k':ORDINAL | _k' LESS _k :: pp(_k', args)
        var smaller = Expression.CreateLess(kprime, k);
        limitCalls = new ForallExpr(pp.Origin, [kprimeVar], smaller, ppCall, triggerAttr) {
          Type = Type.Bool,
          Bounds = [new AllocFreeBoundedPool(kprimeVar.Type)]
        };
      } else {
        // exists k':ORDINAL | _k' LESS _k :: pp(_k', args)
        // Here, instead of using the usual ORD#Less, we use the semantically equivalent ORD#LessThanLimit, because this
        // allows us to write a good trigger for a targeted monotonicity axiom.  That axiom, in turn, makes the
        // automatic verification more powerful for least lemmas that have more than one focal-predicate term.
        var smaller = new BinaryExpr(kprime.Origin, BinaryExpr.Opcode.Lt, kprime, k) {
          ResolvedOp = BinaryExpr.ResolvedOpcode.LessThanLimit,
          Type = Type.Bool
        };
        limitCalls = new ExistsExpr(pp.Origin, [kprimeVar], smaller, ppCall, triggerAttr) {
          Type = Type.Bool,
          Bounds = [new AllocFreeBoundedPool(kprimeVar.Type)]
        };
      }
      var a = Expression.CreateImplies(kIsPositive, body);
      var b = Expression.CreateImplies(kIsLimit, limitCalls);
      return Expression.CreateAnd(a, b);
    } else {
      // 0 < k
      var kIsPositive = Expression.CreateLess(Expression.CreateIntLiteral(pp.Origin, 0), k);
      if (pp.ExtremePred is GreatestPredicate) {
        // add antecedent "0 < _k ==>"
        return Expression.CreateImplies(kIsPositive, body);
      } else {
        // add initial conjunct "0 < _k &&"
        return Expression.CreateAnd(kIsPositive, body);
      }
    }
  }
}