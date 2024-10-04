using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using static Microsoft.Dafny.Util;
using Action = System.Action;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {

  void TrCallStmt(CallStmt s, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, Bpl.IdentifierExpr actualReceiver) {
    Contract.Requires(s != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);
    Contract.Requires(!(s.Method is Constructor) || (s.Lhs.Count == 0 && actualReceiver != null));

    var tySubst = s.MethodSelect.TypeArgumentSubstitutionsWithParents();
    ProcessLhss(s.Lhs, true, true, builder, locals, etran, s, out var lhsBuilders, out var bLhss,
      out _, out _, out _, s.OriginalInitialLhs);
    Contract.Assert(s.Lhs.Count == lhsBuilders.Count);
    Contract.Assert(s.Lhs.Count == bLhss.Count);
    var lhsTypes = new List<Type>();
    if (s.Method is Constructor) {
      lhsTypes.Add(s.Receiver.Type);
      bLhss.Add(actualReceiver);
    } else {
      for (int i = 0; i < s.Lhs.Count; i++) {
        var lhs = s.Lhs[i];
        lhsTypes.Add(lhs.Type);
        builder.Add(new CommentCmd("TrCallStmt: Adding lhs with type " + lhs.Type));
        if (bLhss[i] == null) {  // (in the current implementation, the second parameter "true" to ProcessLhss implies that all bLhss[*] will be null)
          // create temporary local and assign it to bLhss[i]
          string nm = CurrentIdGenerator.FreshId("$rhs##");
          var formalOutType = s.Method.Outs[i].Type.Subst(tySubst);
          var ty = TrType(formalOutType);
          Bpl.LocalVariable var = new Bpl.LocalVariable(lhs.tok, new Bpl.TypedIdent(lhs.tok, nm, ty));
          locals.Add(var);
          bLhss[i] = new Bpl.IdentifierExpr(lhs.tok, var.Name, ty);
        }
      }
    }
    Bpl.IdentifierExpr initHeap = null;
    if (codeContext is IteratorDecl) {
      // var initHeap := $Heap;
      var initHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, CurrentIdGenerator.FreshId("$initHeapCallStmt#"), predef.HeapType));
      locals.Add(initHeapVar);
      initHeap = new Bpl.IdentifierExpr(s.Tok, initHeapVar);
      // initHeap := $Heap;
      builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, initHeap, etran.HeapExpr));
    }
    builder.Add(new CommentCmd("TrCallStmt: Before ProcessCallStmt"));
    ProcessCallStmt(s, tySubst, actualReceiver, bLhss, lhsTypes, builder, locals, etran);
    builder.Add(new CommentCmd("TrCallStmt: After ProcessCallStmt"));
    for (int i = 0; i < lhsBuilders.Count; i++) {
      var lhs = s.Lhs[i];
      Type lhsType, rhsTypeConstraint;
      if (lhs is IdentifierExpr) {
        var ide = (IdentifierExpr)lhs;
        lhsType = ide.Var.Type;
        rhsTypeConstraint = lhsType;
      } else if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
        var field = (Field)fse.Member;
        Contract.Assert(field != null);
        Contract.Assert(VisibleInScope(field));
        lhsType = field.Type;
        rhsTypeConstraint = lhsType.Subst(fse.TypeArgumentSubstitutionsWithParents());
      } else if (lhs is SeqSelectExpr) {
        var e = (SeqSelectExpr)lhs;
        lhsType = null;  // for arrays, always make sure the value assigned is boxed
        rhsTypeConstraint = e.Seq.Type.TypeArgs[0];
      } else {
        var e = (MultiSelectExpr)lhs;
        lhsType = null;  // for arrays, always make sure the value assigned is boxed
        rhsTypeConstraint = e.Array.Type.TypeArgs[0];
      }

      Bpl.Expr bRhs = bLhss[i];  // the RHS (bRhs) of the assignment to the actual call-LHS (lhs) was a LHS (bLhss[i]) in the Boogie call statement
      CheckSubrange(lhs.tok, bRhs, s.Method.Outs[i].Type.Subst(tySubst), rhsTypeConstraint, null, builder);
      bRhs = CondApplyBox(lhs.tok, bRhs, lhs.Type, lhsType);

      lhsBuilders[i](bRhs, false, builder, etran);
    }
    if (codeContext is IteratorDecl) {
      var iter = (IteratorDecl)codeContext;
      Contract.Assert(initHeap != null);
      RecordNewObjectsIn_New(s.Tok, iter, initHeap, etran.HeapCastToIdentifierExpr, builder, locals, etran);
    }
    builder.AddCaptureState(s);
  }

  void ProcessCallStmt(CallStmt cs, Dictionary<TypeParameter, Type> tySubst, Bpl.Expr bReceiver,
    List<Bpl.IdentifierExpr> Lhss, List<Type> LhsTypes,
    BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {

    Contract.Requires(cs != null);
    Contract.Requires(Lhss != null);
    Contract.Requires(LhsTypes != null);
    // Note, a Dafny class constructor is declared to have no output parameters, but it is encoded in Boogie as
    // having an output parameter.
    Contract.Requires(cs.Method is Constructor || cs.Method.Outs.Count == Lhss.Count);
    Contract.Requires(cs.Method is Constructor || cs.Method.Outs.Count == LhsTypes.Count);
    Contract.Requires(!(cs.Method is Constructor) || (cs.Method.Outs.Count == 0 && Lhss.Count == 1 && LhsTypes.Count == 1));
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);
    Contract.Requires(tySubst != null);
    var tok = GetToken(cs);
    var tyArgs = GetTypeParams(cs.Method);
    var dafnyReceiver = cs.Receiver;
    var method = cs.Method;
    var atLabel = cs.MethodSelect.AtLabel;
    var Args = cs.Args;

    // Figure out if the call is recursive or not, which will be used below to determine the need for a
    // termination check and the need to include an implicit _k-1 argument.
    bool isRecursiveCall = false;
    // consult the call graph to figure out if this is a recursive call
    var module = method.EnclosingClass.EnclosingModuleDefinition;
    if (codeContext != null && module == currentModule) {
      // Note, prefix lemmas are not recorded in the call graph, but their corresponding greatest lemmas are.
      // Similarly, an iterator is not recorded in the call graph, but its MoveNext method is.
      ICallable cllr =
        codeContext is PrefixLemma ? ((PrefixLemma)codeContext).ExtremeLemma :
        codeContext is IteratorDecl ? ((IteratorDecl)codeContext).Member_MoveNext :
        codeContext;
      if (ModuleDefinition.InSameSCC(method, cllr)) {
        isRecursiveCall = true;
      }
    }

    bool isCoCall = false;
    var callee = method;
    if (method is ExtremeLemma && isRecursiveCall) {
      isCoCall = true;
      callee = ((ExtremeLemma)method).PrefixLemma;
    } else if (method is PrefixLemma) {
      // an explicit call to a prefix lemma is allowed only inside the SCC of the corresponding greatest lemma,
      // so we consider this to be a co-call
      isCoCall = true;
    }

    var ins = new List<Bpl.Expr>();
    if (callee is TwoStateLemma) {
      ins.Add(etran.OldAt(atLabel).HeapExpr);
      ins.Add(etran.HeapExpr);
    }
    // Add type arguments
    ins.AddRange(TrTypeArgs(tySubst, tyArgs));

    // Translate receiver argument, if any
    Expression receiver = bReceiver == null ? dafnyReceiver : new BoogieWrapper(bReceiver, dafnyReceiver.Type);
    if (!method.IsStatic && method is not Constructor) {
      if (bReceiver == null) {
        TrStmt_CheckWellformed(dafnyReceiver, builder, locals, etran, true);
        if (!(dafnyReceiver is ThisExpr)) {
          CheckNonNull(dafnyReceiver.tok, dafnyReceiver, builder, etran, null);
        }
      }
      var obj = etran.TrExpr(receiver);
      if (bReceiver == null) {
        obj = BoxifyForTraitParent(tok, obj, method, dafnyReceiver.Type);
      }
      ins.Add(obj);
    } else if (receiver is StaticReceiverExpr stexpr) {
      if (stexpr.ObjectToDiscard != null) {
        TrStmt_CheckWellformed(stexpr.ObjectToDiscard, builder, locals, etran, true);
      }
    }

    // Ideally, the modifies and decreases checks would be done after the precondition check,
    // but Boogie doesn't give us a hook for that.  So, we set up our own local variables here to
    // store the actual parameters.
    // Create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
    var substMap = new Dictionary<IVariable, Expression>();
    var directSubstMap = new Dictionary<IVariable, Expression>();
    for (int i = 0; i < callee.Ins.Count; i++) {
      var formal = callee.Ins[i];
      var local = new LocalVariable(formal.RangeToken, formal.Name + "#", formal.Type.Subst(tySubst), formal.IsGhost);
      local.type = local.SyntacticType;  // resolve local here
      var ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
      ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
      substMap.Add(formal, ie);
      locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type))));

      var param = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
      Bpl.Expr bActual;
      Expression dActual;
      if (i == 0 && method is ExtremeLemma && isRecursiveCall) {
        // Treat this call to M(args) as a call to the corresponding prefix lemma M#(_k - 1, args), so insert an argument here.
        var k = ((PrefixLemma)callee).K;
        var bplK = new Bpl.IdentifierExpr(k.tok, k.AssignUniqueName(currentDeclaration.IdGenerator), TrType(k.Type));
        dActual = Expression.CreateSubtract(Expression.CreateIdentExpr(k), Expression.CreateNatLiteral(k.tok, 1, k.Type));
        if (k.Type.IsBigOrdinalType) {
          bActual = FunctionCall(k.tok, "ORD#Minus", predef.BigOrdinalType,
            bplK,
            FunctionCall(k.tok, "ORD#FromNat", predef.BigOrdinalType, Bpl.Expr.Literal(1)));
        } else {
          bActual = Bpl.Expr.Sub(bplK, Bpl.Expr.Literal(1));
        }
      } else {
        Expression actual;
        if (method is ExtremeLemma && isRecursiveCall) {
          actual = Args[i - 1];
        } else {
          actual = Args[i];
        }
        if (!(actual is DefaultValueExpression)) {
          TrStmt_CheckWellformed(actual, builder, locals, etran, true);
        }
        builder.Add(new CommentCmd("ProcessCallStmt: CheckSubrange"));
        // Check the subrange without boxing
        var beforeBox = etran.TrExpr(actual);
        CheckSubrange(actual.tok, beforeBox, actual.Type, formal.Type.Subst(tySubst), actual, builder);
        bActual = AdaptBoxing(actual.tok, beforeBox, actual.Type, formal.Type.Subst(tySubst));
        dActual = actual;
      }
      directSubstMap.Add(formal, dActual);
      Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(formal.tok, param, bActual);
      builder.Add(cmd);
      ins.Add(AdaptBoxing(ToDafnyToken(flags.ReportRanges, param.tok), param, formal.Type.Subst(tySubst), formal.Type));
    }

    // Check that every parameter is available in the state in which the method is invoked; this means checking that it has
    // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
    // access to expressions of the appropriate type and that are allocated in the current state.  However, if the method is
    // invoked in the 'old' state or if the method invoked is a two-state lemma with a non-new parameter, then we need to
    // check that its arguments were all available at that time as well.
    if (etran.UsesOldHeap) {
      if (!method.IsStatic && !(method is Constructor)) {
        Bpl.Expr wh = GetWhereClause(receiver.tok, etran.TrExpr(receiver), receiver.Type, etran, ISALLOC, true);
        if (wh != null) {
          var desc = new PODesc.IsAllocated("receiver argument", "in the state in which the method is invoked", receiver);
          builder.Add(Assert(receiver.tok, wh, desc));
        }
      }
      for (int i = 0; i < Args.Count; i++) {
        Expression ee = Args[i];
        Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
        if (wh != null) {
          var desc = new PODesc.IsAllocated("argument", "in the state in which the method is invoked", ee);
          builder.Add(Assert(ee.tok, wh, desc));
        }
      }
    } else if (method is TwoStateLemma) {
      if (!method.IsStatic) {
        Bpl.Expr wh = GetWhereClause(receiver.tok, etran.TrExpr(receiver), receiver.Type, etran.OldAt(atLabel), ISALLOC, true);
        if (wh != null) {
          var desc = new PODesc.IsAllocated("receiver argument", "in the two-state lemma's previous state", receiver, atLabel);
          builder.Add(Assert(receiver.tok, wh, desc));
        }
      }
      Contract.Assert(callee.Ins.Count == Args.Count);
      for (int i = 0; i < Args.Count; i++) {
        var formal = callee.Ins[i];
        if (formal.IsOld) {
          Expression ee = Args[i];
          Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran.OldAt(atLabel), ISALLOC, true);
          if (wh != null) {
            var pIdx = Args.Count == 1 ? "" : " at index " + i;
            var desc = new PODesc.IsAllocated(
              $"argument{pIdx} for parameter '{formal.Name}'",
              "in the two-state lemma's previous state" + PODesc.IsAllocated.HelperFormal(formal),
              ee,
              atLabel
            );
            builder.Add(Assert(ee.tok, wh, desc));
          }
        }
      }
    }

    var directSub = new Substituter(null, directSubstMap, tySubst);

    // Check that the reads clause of a subcall is a subset of the current reads frame,
    // but support the optimization that we don't define a reads frame at all if it's `reads *`. 
    if (etran.readsFrame != null) {
      // substitute actual args for parameters in description expression frames...
      var requiredFrames = callee.Reads.Expressions.ConvertAll(directSub.SubstFrameExpr);
      var desc = new PODesc.ReadFrameSubset("call", requiredFrames, GetContextReadsFrames());

      // ... but that substitution isn't needed for frames passed to CheckFrameSubset
      var readsSubst = new Substituter(null, new Dictionary<IVariable, Expression>(), tySubst);
      CheckFrameSubset(tok, callee.Reads.Expressions.ConvertAll(readsSubst.SubstFrameExpr),
        receiver, substMap, etran, etran.ReadsFrame(tok), builder, desc, null);
    }

    // substitute actual args for parameters in description expression frames...
    var frameExpressions = callee.Mod.Expressions.ConvertAll(directSub.SubstFrameExpr);
    // Check that the modifies clause of a subcall is a subset of the current modifies frame,
    // but only if we're in a context that defines a modifies frame.
    if (codeContext is IMethodCodeContext methodCodeContext) {
      var desc = new PODesc.ModifyFrameSubset(
        "call",
        frameExpressions,
        methodCodeContext.Modifies.Expressions
      );
      // ... but that substitution isn't needed for frames passed to CheckFrameSubset
      var modifiesSubst = new Substituter(null, new(), tySubst);
      CheckFrameSubset(
        tok, callee.Mod.Expressions.ConvertAll(modifiesSubst.SubstFrameExpr),
        receiver, substMap, etran, etran.ModifiesFrame(tok), builder, desc, null);
    }

    // Check termination
    if (isRecursiveCall) {
      Contract.Assert(codeContext != null);
      if (codeContext is DatatypeDecl) {
        builder.Add(Assert(tok, Bpl.Expr.False, new PODesc.IsNonRecursive()));
      } else {
        List<Expression> contextDecreases = codeContext.Decreases.Expressions;
        List<Expression> calleeDecreases = callee.Decreases.Expressions;
        CheckCallTermination(tok, contextDecreases, calleeDecreases, null, receiver, substMap, directSubstMap, tySubst, etran, true, builder, codeContext.InferredDecreases, null);
      }
    }

    // Create variables to hold the output parameters of the call, so that appropriate unboxes can be introduced.
    var outs = new List<Bpl.IdentifierExpr>();
    var tmpOuts = new List<Bpl.IdentifierExpr>();
    if (method is Constructor) {
      tmpOuts.Add(null);
      outs.Add(Lhss[0]);
    } else {
      for (int i = 0; i < Lhss.Count; i++) {
        var bLhs = Lhss[i];
        if (ModeledAsBoxType(callee.Outs[i].Type) && !ModeledAsBoxType(LhsTypes[i])) {
          // we need an Unbox
          Bpl.LocalVariable var = new Bpl.LocalVariable(bLhs.tok, new Bpl.TypedIdent(bLhs.tok, CurrentIdGenerator.FreshId("$tmp##"), predef.BoxType));
          locals.Add(var);
          Bpl.IdentifierExpr varIdE = new Bpl.IdentifierExpr(bLhs.tok, var.Name, predef.BoxType);
          tmpOuts.Add(varIdE);
          outs.Add(varIdE);
        } else {
          tmpOuts.Add(null);
          outs.Add(bLhs);
        }
      }
    }

    if (cs.Proof == null) {
      AddCall(builder);
    } else {
      var callBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
      AddComment(callBuilder, cs, "call statement proof");
      CurrentIdGenerator.Push();
      TrStmt(cs.Proof, callBuilder, locals, etran);
      CurrentIdGenerator.Pop();
      AddCall(callBuilder);
      PathAsideBlock(cs.Tok, callBuilder, builder);
    }

    void AddCall(BoogieStmtListBuilder callBuilder) {
      callBuilder.Add(new CommentCmd($"ProcessCallStmt: Check precondition"));
      // Make the call
      AddReferencedMember(callee);
      var call = Call(tok, MethodName(callee, isCoCall ? MethodTranslationKind.CoCallPre : MethodTranslationKind.CallPre), ins, new List<Bpl.IdentifierExpr>());
      proofDependencies?.AddProofDependencyId(call, tok, new CallDependency(cs));
      if (
        (assertionOnlyFilter != null && !assertionOnlyFilter(tok)) ||
        (module != currentModule && RefinementToken.IsInherited(tok, currentModule) && (codeContext == null || !codeContext.MustReverify))) {
        // The call statement is inherited, so the refined module already checked that the precondition holds.  Note,
        // preconditions are not allowed to be strengthened, except if they use a predicate whose body has been strengthened.
        // But if the callee sits in a different module, then any predicate it uses will be treated as opaque (that is,
        // uninterpreted) anyway, so the refined module will have checked the call precondition for all possible definitions
        // of the predicate.
        call.IsFree = true;
      }
      callBuilder.Add(call);
    }

    builder.Add(new CommentCmd("ProcessCallStmt: Make the call"));
    var post = Call(tok,
      MethodName(callee, isCoCall ? MethodTranslationKind.CoCallPost : MethodTranslationKind.CallPost), ins, outs);
    proofDependencies?.AddProofDependencyId(post, tok, new CallDependency(cs));
    builder.Add(post);

    // Unbox results as needed
    for (int i = 0; i < Lhss.Count; i++) {
      Bpl.IdentifierExpr bLhs = Lhss[i];
      Bpl.IdentifierExpr tmpVarIdE = tmpOuts[i];
      if (tmpVarIdE != null) {
        // Instead of an assignment:
        //    e := UnBox(tmpVar);
        // we use:
        //    havoc e; assume e == UnBox(tmpVar);
        // because that will reap the benefits of e's where clause, so that some additional type information will be known about
        // the out-parameter.
        Bpl.Cmd cmd = new Bpl.HavocCmd(bLhs.tok, new List<Bpl.IdentifierExpr> { bLhs });
        builder.Add(cmd);
        cmd = TrAssumeCmd(bLhs.tok, Bpl.Expr.Eq(bLhs, FunctionCall(bLhs.tok, BuiltinFunction.Unbox, TrType(LhsTypes[i]), tmpVarIdE)));
        builder.Add(cmd);
      }
    }
  }
}