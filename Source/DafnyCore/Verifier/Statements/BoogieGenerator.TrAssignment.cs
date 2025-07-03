using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {


  /// <summary>
  /// "lhs" is expected to be a resolved form of an expression, i.e., not a concrete-syntax expression.
  /// </summary>
  void TrAssignment(Statement stmt, Expression lhs, AssignmentRhs rhs,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
    Contract.Requires(stmt != null);
    Contract.Requires(lhs != null);
    Contract.Requires(!(lhs is ConcreteSyntaxExpression));
    Contract.Requires(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // these were once allowed, but their functionality is now provided by 'forall' statements
    Contract.Requires(rhs != null);
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(Predef != null);

    var lhss = new List<Expression>() { lhs };
    ProcessLhss(lhss, rhs.CanAffectPreviouslyKnownExpressions, true, builder, locals, etran, stmt,
      out var lhsBuilder, out var bLhss, out var ignore1, out var ignore2, out var ignore3);
    Contract.Assert(lhsBuilder.Count == 1 && bLhss.Count == 1);  // guaranteed by postcondition of ProcessLhss

    var rhss = new List<AssignmentRhs>() { rhs };
    ProcessRhss(lhsBuilder, bLhss, lhss, rhss, builder, locals, etran, stmt);
    builder.AddCaptureState(stmt);
  }

  void ProcessRhss(List<AssignToLhs> lhsBuilder, List<Bpl.IdentifierExpr/*may be null*/> bLhss,
    List<Expression> lhss, List<AssignmentRhs> rhss,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran, Statement stmt) {
    Contract.Requires(lhsBuilder != null);
    Contract.Requires(bLhss != null);
    Contract.Requires(Cce.NonNullElements(lhss));
    Contract.Requires(Cce.NonNullElements(rhss));
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(Predef != null);

    var finalRhss = new List<Bpl.Expr>();
    for (int i = 0; i < lhss.Count; i++) {
      var lhs = lhss[i];
      // the following assumes are part of the precondition, really
      Contract.Assume(!(lhs is ConcreteSyntaxExpression));
      Contract.Assume(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // array-range assignments are not allowed

      Type lhsType, rhsTypeConstraint;
      if (lhs is IdentifierExpr) {
        var ide = (IdentifierExpr)lhs;
        lhsType = ide.Var.Type;
        rhsTypeConstraint = lhsType;
      } else if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
        var field = (Field)fse.Member;
        Contract.Assert(VisibleInScope(field));
        lhsType = field.Type;
        rhsTypeConstraint = lhsType.Subst(fse.TypeArgumentSubstitutionsWithParents());
      } else if (lhs is SeqSelectExpr) {
        var e = (SeqSelectExpr)lhs;
        lhsType = null;  // for an array update, always make sure the value assigned is boxed
        rhsTypeConstraint = e.Seq.Type.NormalizeExpand().TypeArgs[0];
      } else {
        var e = (MultiSelectExpr)lhs;
        lhsType = null;  // for an array update, always make sure the value assigned is boxed
        rhsTypeConstraint = e.Array.Type.NormalizeExpand().TypeArgs[0];
      }
      var bRhs = TrAssignmentRhs(rhss[i].Origin, bLhss[i], null, lhsType, rhss[i], rhsTypeConstraint, builder, locals, etran, stmt);
      if (bLhss[i] != null) {
        Contract.Assert(bRhs == bLhss[i]);  // this is what the postcondition of TrAssignmentRhs promises
        // assignment has already been done by TrAssignmentRhs
        finalRhss.Add(null);
      } else {
        Contract.Assert(bRhs != null);  // this is what the postcondition of TrAssignmentRhs promises
        finalRhss.Add(bRhs);
      }
    }
    for (int i = 0; i < lhss.Count; i++) {
      lhsBuilder[i](finalRhss[i], rhss[i] is HavocRhs, builder, etran);
    }
  }

  List<Bpl.Expr> ProcessUpdateAssignRhss(List<Expression> lhss, List<AssignmentRhs> rhss,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
    Statement stmt) {
    Contract.Requires(Cce.NonNullElements(lhss));
    Contract.Requires(Cce.NonNullElements(rhss));
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(Predef != null);
    Contract.Ensures(Contract.ForAll(Contract.Result<List<Bpl.Expr>>(), i => i != null));

    var finalRhss = new List<Bpl.Expr>();
    for (int i = 0; i < lhss.Count; i++) {
      var lhs = lhss[i];
      // the following assumes are part of the precondition, really
      Contract.Assume(!(lhs is ConcreteSyntaxExpression));
      Contract.Assume(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // array-range assignments are not allowed

      Type lhsType, rhsTypeConstraint;
      if (lhs is IdentifierExpr) {
        lhsType = ((IdentifierExpr)lhs).Var.Type;
        rhsTypeConstraint = lhsType;
      } else if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
        var field = (Field)fse.Member;
        Contract.Assert(VisibleInScope(field));
        lhsType = field.Type;
        rhsTypeConstraint = lhsType.Subst(fse.TypeArgumentSubstitutionsWithParents());
      } else if (lhs is SeqSelectExpr) {
        var e = (SeqSelectExpr)lhs;
        lhsType = null;  // for an array update, always make sure the value assigned is boxed
        rhsTypeConstraint = e.Seq.Type.NormalizeExpand().TypeArgs[0];
      } else {
        var e = (MultiSelectExpr)lhs;
        lhsType = null;  // for an array update, always make sure the value assigned is boxed
        rhsTypeConstraint = e.Array.Type.NormalizeExpand().TypeArgs[0];
      }
      var bRhs = TrAssignmentRhs(rhss[i].Origin, null, (lhs as IdentifierExpr)?.Var, lhsType, rhss[i], rhsTypeConstraint, builder, locals, etran, stmt);
      finalRhss.Add(bRhs);
    }
    return finalRhss;
  }


  private void CheckLhssDistinctness(List<Bpl.Expr> rhs, List<AssignmentRhs> rhsOriginal, List<Expression> lhss,
    BoogieStmtListBuilder builder, ExpressionTranslator etran,
    Bpl.Expr[] objs, Bpl.Expr[] fields, string[] names, Expression originalInitialLhs = null) {
    Contract.Requires(rhs != null);
    Contract.Requires(rhsOriginal != null);
    Contract.Requires(lhss != null);
    Contract.Requires(rhs.Count == rhsOriginal.Count);
    Contract.Requires(lhss.Count == rhsOriginal.Count);
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(Predef != null);

    for (int i = 0; i < lhss.Count; i++) {
      var lhs = lhss[i];
      Contract.Assume(!(lhs is ConcreteSyntaxExpression));
      if (originalInitialLhs != null) {
        // TODO - check RHS values?
        AssertDistinctness(lhs, originalInitialLhs, builder, etran);
      }
      for (int j = 0; j < i; j++) {
        if (rhsOriginal[i] is HavocRhs || rhsOriginal[j] is HavocRhs) {
          AssertDistinctness(lhs, lhss[j], builder, etran);
        } else {
          AssertDistinctness(lhs, lhss[j], rhs[i], rhs[j], builder, etran);
        }
      }
    }
  }

  /// <summary>
  /// Note, if "rhs" is "null", then the assignment has already been done elsewhere. However, any other bookkeeping
  /// is still done.
  /// </summary>
  delegate void AssignToLhs(Bpl.Expr/*?*/ rhs, bool origRhsIsHavoc, BoogieStmtListBuilder builder, ExpressionTranslator etran);

  void AssertDistinctness(Expression lhsa, Expression lhsb, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
    CheckDistinctness(lhsa, lhsb, etran, out var dExpr, out var bExpr);
    if (bExpr != null) {
      builder.Add(Assert(GetToken(lhsa), bExpr, new DistinctLHS(Printer.ExprToString(options, lhsa),
        Printer.ExprToString(options, lhsb), bExpr != Bpl.Expr.False, false, dExpr), builder.Context));
    }
  }

  void AssertDistinctness(Expression lhsa, Expression lhsb, Bpl.Expr rhsa, Bpl.Expr rhsb, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
    CheckDistinctness(lhsa, lhsb, etran, out var dExpr, out var bExpr);
    if (bExpr != null) {
      bExpr = BplOr(bExpr, Bpl.Expr.Eq(rhsa, rhsb));
      builder.Add(Assert(GetToken(lhsa), bExpr, new DistinctLHS(Printer.ExprToString(options, lhsa),
        Printer.ExprToString(options, lhsb), false, true, dExpr), builder.Context));
    }
  }

  /// <summary>
  /// Creates a list of protected Boogie LHSs for the given Dafny LHSs.  Along the way,
  /// builds code that checks that the LHSs are well-defined,
  /// and are allowed by the enclosing reads and modifies clause.
  /// Checks that they denote different locations iff checkDistinctness is true.
  /// </summary>
  void ProcessLhss(List<Expression> lhss, bool rhsCanAffectPreviouslyKnownExpressions, bool checkDistinctness,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran, Statement stmt,
    out List<AssignToLhs> lhsBuilders, out List<Bpl.IdentifierExpr/*may be null*/> bLhss,
    out Bpl.Expr[] prevObj, out Bpl.Expr[] prevIndex, out string[] prevNames, Expression originalInitialLhs = null) {

    Contract.Requires(Cce.NonNullElements(lhss));
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(Predef != null);
    Contract.Ensures(Contract.ValueAtReturn(out lhsBuilders).Count == lhss.Count);
    Contract.Ensures(Contract.ValueAtReturn(out lhsBuilders).Count == Contract.ValueAtReturn(out bLhss).Count);

    rhsCanAffectPreviouslyKnownExpressions = rhsCanAffectPreviouslyKnownExpressions || lhss.Count != 1;

    // for each Dafny LHS, build a protected Boogie LHS for the eventual assignment
    lhsBuilders = [];
    bLhss = [];
    prevObj = new Bpl.Expr[lhss.Count];
    prevIndex = new Bpl.Expr[lhss.Count];
    prevNames = new string[lhss.Count];
    int i = 0;

    var lhsNameSet = new Dictionary<string, object>();

    var contextModFrames = GetContextModifiesFrames();

    // Note, the resolver does not check for duplicate IdentifierExpr's in LHSs, so do it here.
    foreach (var lhs in lhss) {
      Contract.Assume(!(lhs is ConcreteSyntaxExpression));
      if (checkDistinctness) {
        if (originalInitialLhs != null) {
          AssertDistinctness(lhs, originalInitialLhs.Resolved, builder, etran);
        }
        for (int j = 0; j < i; j++) {
          AssertDistinctness(lhs, lhss[j], builder, etran);
        }
      }
      i++;
    }

    i = 0;
    foreach (var lhs in lhss) {
      IOrigin tok = lhs.Origin;
      TrStmt_CheckWellformed(lhs, builder, locals, etran, true, true);

      if (lhs is IdentifierExpr) {
        var ie = (IdentifierExpr)lhs;
        prevNames[i] = ie.Name;
        var bLhs = (Bpl.IdentifierExpr)etran.TrExpr(lhs);  // TODO: is this cast always justified?
        bLhss.Add(rhsCanAffectPreviouslyKnownExpressions ? null : bLhs);
        lhsBuilders.Add(delegate (Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
          if (rhs != null) {
            var cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, rhs);
            proofDependencies?.AddProofDependencyId(cmd, lhs.Origin, new AssignmentDependency(stmt.Origin));
            bldr.Add(cmd);
          }

          if (!origRhsIsHavoc || ie.Type.HavocCountsAsDefiniteAssignment(ie.Var.IsGhost)) {
            MarkDefiniteAssignmentTracker(ie, bldr);
          }
        });

      } else if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
        var field = fse.Member as Field;
        Contract.Assert(field != null);
        Contract.Assert(VisibleInScope(field));

        var useSurrogateLocal = inBodyInitContext && Expression.AsThis(fse.Obj) != null;

        var obj = SaveInTemp(etran.TrExpr(fse.Obj), rhsCanAffectPreviouslyKnownExpressions,
          "$obj" + i, Predef.RefType, builder, locals);
        prevObj[i] = obj;
        if (!useSurrogateLocal) {
          // check that the enclosing modifies clause allows this object to be written:  assert $_ModifiesFrame[obj]);
          var desc = new Modifiable("an object", contextModFrames, fse.Obj, field);
          builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.ModifiesFrame(tok), obj, GetField(fse)), desc, builder.Context));
        }

        if (useSurrogateLocal) {
          var nm = SurrogateName(field);
          var bLhs = new Bpl.IdentifierExpr(fse.Origin, nm, TrType(field.Type));
          bLhss.Add(rhsCanAffectPreviouslyKnownExpressions ? null : bLhs);
          lhsBuilders.Add(delegate (Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
            if (rhs != null) {
              var cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, rhs);
              proofDependencies?.AddProofDependencyId(cmd, fse.Origin, new AssignmentDependency(stmt.Origin));
              bldr.Add(cmd);
            }

            if (!origRhsIsHavoc || field.Type.HavocCountsAsDefiniteAssignment(field.IsGhost)) {
              MarkDefiniteAssignmentTracker(lhs.Origin, nm, bldr);
            }
          });
        } else {
          bLhss.Add(null);
          lhsBuilders.Add(delegate (Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
            if (rhs != null) {
              var fseField = fse.Member as Field;
              Contract.Assert(fseField != null);
              Check_NewRestrictions(tok, fse.Obj, obj, fseField, rhs, bldr, et);
              var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
              var cmd = Bpl.Cmd.SimpleAssign(tok, h, UpdateHeap(tok, h, obj, new Bpl.IdentifierExpr(tok, GetField(fseField)), rhs));
              proofDependencies?.AddProofDependencyId(cmd, lhs.Origin, new AssignmentDependency(stmt.Origin));
              bldr.Add(cmd);
              // assume $IsGoodHeap($Heap);
              bldr.Add(AssumeGoodHeap(tok, et));
            }
          });
        }

      } else if (lhs is SeqSelectExpr) {
        SeqSelectExpr sel = (SeqSelectExpr)lhs;
        Contract.Assert(sel.SelectOne);  // array-range assignments are not allowed
        Contract.Assert(sel.Seq.Type != null && sel.Seq.Type.IsArrayType);
        Contract.Assert(sel.E0 != null);
        var obj = SaveInTemp(etran.TrExpr(sel.Seq), rhsCanAffectPreviouslyKnownExpressions,
          "$obj" + i, Predef.RefType, builder, locals);
        var idx = etran.TrExpr(sel.E0);
        idx = ConvertExpression(sel.E0.Origin, idx, sel.E0.Type, Type.Int);
        var fieldName = SaveInTemp(FunctionCall(tok, BuiltinFunction.IndexField, null, idx), rhsCanAffectPreviouslyKnownExpressions,
          "$index" + i, Predef.FieldName(tok), builder, locals);
        prevObj[i] = obj;
        prevIndex[i] = fieldName;
        // check that the enclosing modifies clause allows this object to be written:  assert $_Frame[obj,index]);
        var desc = new Modifiable("an array element", contextModFrames, sel.Seq, null);
        builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.ModifiesFrame(tok), obj, fieldName), desc, builder.Context));

        bLhss.Add(null);
        lhsBuilders.Add(delegate (Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
          if (rhs != null) {
            var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
            var cmd = Bpl.Cmd.SimpleAssign(tok, h, UpdateHeap(tok, h, obj, fieldName, rhs));
            proofDependencies?.AddProofDependencyId(cmd, lhs.Origin, new AssignmentDependency(stmt.Origin));
            bldr.Add(cmd);
            // assume $IsGoodHeap($Heap);
            bldr.Add(AssumeGoodHeap(tok, et));
          }
        });

      } else {
        MultiSelectExpr mse = (MultiSelectExpr)lhs;
        Contract.Assert(mse.Array.Type != null && mse.Array.Type.IsArrayType);

        var obj = SaveInTemp(etran.TrExpr(mse.Array), rhsCanAffectPreviouslyKnownExpressions,
          "$obj" + i, Predef.RefType, builder, locals);
        var fieldName = SaveInTemp(etran.GetArrayIndexFieldName(mse.Origin, mse.Indices), rhsCanAffectPreviouslyKnownExpressions,
          "$index" + i, Predef.FieldName(mse.Origin), builder, locals);
        prevObj[i] = obj;
        prevIndex[i] = fieldName;
        var desc = new Modifiable("an array element", contextModFrames, mse.Array, null);
        builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.ModifiesFrame(tok), obj, fieldName), desc, builder.Context));

        bLhss.Add(null);
        lhsBuilders.Add(delegate (Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
          if (rhs != null) {
            var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
            var cmd = Bpl.Cmd.SimpleAssign(tok, h, UpdateHeap(tok, h, obj, fieldName, rhs));
            proofDependencies?.AddProofDependencyId(cmd, lhs.Origin, new AssignmentDependency(stmt.Origin));
            bldr.Add(cmd);
            // assume $IsGoodHeap($Heap);
            bldr.Add(AssumeGoodHeap(tok, etran));
          }
        });
      }

      i++;
    }
  }

  /// <summary>
  /// if "bGivenLhs" is non-null, generates an assignment of the translation of "rhs" to "bGivenLhs" and then returns "bGivenLhs".
  /// If "bGivenLhs" is null, then this method will return an expression that in a stable way denotes the translation of "rhs";
  /// this is achieved by creating a new temporary Boogie variable to hold the result and returning an expression that mentions
  /// that new temporary variable.
  ///
  /// Before the assignment, the generated code will check that "rhs" obeys any subrange requirements entailed by "rhsTypeConstraint".
  ///
  /// The purpose of "lhsVar" is to determine an appropriate Boogie "where" clause for any temporary variable generated.
  /// If passed in as non-null, it says that "lhsVar" is the LHS of the assignment being translated. If the type is subject to
  /// definite-assignment rules and the RHS is "*", then the "where" clause of the temporary variable will have the form
  /// "defass#lhs ==> wh" where "defass#lhs" is the definite-assignment tracker for "lhsVar" and "wh" is the "where"
  /// clause for type "lhsType" for the temporary variable.
  ///
  /// The purpose of "lhsType" is to determine if the expression should be boxed before doing the assignment.  It is allowed to be null,
  /// which indicates that the result should always be a box.  Note that "lhsType" may refer to a formal type parameter that is not in
  /// scope; this is okay, since the purpose of "lhsType" is just to say whether or not the result should be boxed.
  /// </summary>
  Bpl.Expr TrAssignmentRhs(IOrigin tok, Bpl.IdentifierExpr bGivenLhs, IVariable lhsVar, Type lhsType,
    AssignmentRhs rhs, Type rhsTypeConstraint,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
    Statement stmt) {
    Contract.Requires(tok != null);
    Contract.Requires(rhs != null);
    Contract.Requires(rhsTypeConstraint != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);
    Contract.Requires(Predef != null);
    Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
    Contract.Ensures(bGivenLhs == null || Contract.Result<Bpl.Expr>() == bGivenLhs);

    Bpl.IdentifierExpr bLhs;
    if (bGivenLhs != null) {
      bLhs = bGivenLhs;
    } else {
      Type localType = rhsTypeConstraint;  // this is a type that is appropriate for capturing the value of the RHS
      var ty = TrType(localType);
      var nm = CurrentIdGenerator.FreshId("$rhs#");
      Bpl.Expr wh;
      if (rhs is HavocRhs && localType.IsNonempty) {
        wh = GetWhereClause(tok, new Bpl.IdentifierExpr(tok, nm, ty), localType, etran, NOALLOC);
      } else if (rhs is HavocRhs && lhsVar != null && GetDefiniteAssignmentTracker(lhsVar) != null) {
        // This "where" clause expresses that the new variable has a value of the given type only if
        // the variable has already been definitely assigned. (If it has not already been assigned,
        // then the variable will get a new value, but Dafny's definite-assginment rules prevent that
        // value from being used, so it's appropriate to use effectively-"true" as the "where" clause
        // in that case.
        wh = BplImp(GetDefiniteAssignmentTracker(lhsVar),
          GetWhereClause(tok, new Bpl.IdentifierExpr(tok, nm, ty), localType, etran, NOALLOC));
      } else {
        // In this case, it could be unsound to use a "where" clause, see issue #1619.
        // Luckily, leaving it out is harmless, because we don't need a "where" clause here in the first
        // place--because the variable is short lived, we know it will not be havoc'ed by Boogie, so a
        // "where" wouldn't provide additional information over the assigned value.
        wh = null;
      }
      var v = locals.GetOrCreate(nm, () => new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, nm, ty, wh)));
      bLhs = new Bpl.IdentifierExpr(tok, v);
    }

    if (rhs is ExprRhs) {
      var e = (ExprRhs)rhs;

      var bRhs = etran.TrExpr(e.Expr);
      var cre = GetSubrangeCheck(tok, bRhs, e.Expr.Type, rhsTypeConstraint, e.Expr, null, out var desc, "");
      TrStmt_CheckWellformed(e.Expr, builder, locals, etran, true, addResultCommands:
        (returnBuilder, result) => {
          if (cre != null) {
            returnBuilder.Add(Assert(result.Origin, cre, desc, builder.Context));
          }
        });

      if (bGivenLhs != null) {
        Contract.Assert(bGivenLhs == bLhs);
        // box the RHS, then do the assignment
        var cmd = Bpl.Cmd.SimpleAssign(tok, bGivenLhs, AdaptBoxing(tok, bRhs, e.Expr.Type, lhsType));
        proofDependencies?.AddProofDependencyId(cmd, tok, new AssignmentDependency(stmt.Origin));
        builder.Add(cmd);
        return bGivenLhs;
      } else {
        // box from RHS type to tmp-var type, then do the assignment; then return LHS, boxed from tmp-var type to result type
        var cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, AdaptBoxing(tok, bRhs, e.Expr.Type, rhsTypeConstraint));
        proofDependencies?.AddProofDependencyId(cmd, tok, new AssignmentDependency(stmt.Origin));
        builder.Add(cmd);
        return CondApplyBox(tok, bLhs, rhsTypeConstraint, lhsType);
      }

    } else if (rhs is HavocRhs) {
      builder.Add(new Bpl.HavocCmd(tok, [bLhs]));
      return CondApplyBox(tok, bLhs, rhsTypeConstraint, lhsType);
    } else if (rhs is AllocateClass allocateClass) {
      var callsConstructor = allocateClass.InitCall is { Method: Constructor };
      Bpl.IdentifierExpr nw = GetNewVar_IdExpr(tok, locals);
      if (!callsConstructor) {
        SelectAllocateObject(tok, nw, allocateClass.Type, true, builder, etran);
        Bpl.Cmd heapAllocationRecorder = null;
        if (codeContext is IteratorDecl iter) {
          // $Heap[this, _new] := Set#UnionOne($Heap[this, _new], $Box($nw));
          var th = new Bpl.IdentifierExpr(tok, etran.This, Predef.RefType);
          var nwField = new Bpl.IdentifierExpr(tok, GetField(iter.Member_New));
          var thisDotNew = ApplyUnbox(tok, ReadHeap(tok, etran.HeapExpr, th, nwField), Predef.SetType);
          var unionOne = FunctionCall(tok, BuiltinFunction.SetUnionOne, Predef.BoxType, thisDotNew, ApplyBox(tok, nw));
          var heapRhs = UpdateHeap(tok, etran.HeapExpr, th, nwField, unionOne);
          heapAllocationRecorder = Bpl.Cmd.SimpleAssign(tok, etran.HeapCastToIdentifierExpr, heapRhs);
        }
        CommitAllocatedObject(tok, nw, heapAllocationRecorder, builder, etran);
      }
      if (allocateClass.InitCall != null) {
        AddComment(builder, allocateClass.InitCall, "init call statement");
        TrCallStmt(allocateClass.InitCall, builder, locals, etran, nw);
      }
      // bLhs := $nw;
      CheckSubrange(tok, nw, allocateClass.Type, rhsTypeConstraint, null, builder);
      return HandleGivenLhs(tok, bGivenLhs, lhsType, builder, stmt, bLhs, nw, allocateClass);
    } else if (rhs is AllocateArray allocateArray) {
      int j = 0;
      foreach (Expression dim in allocateArray.ArrayDimensions) {
        CheckWellformed(dim, new WFOptions(), locals, builder, etran);
        var desc = new NonNegative(allocateArray.ArrayDimensions.Count == 1
          ? "array size" : $"array size (dimension {j})", dim);
        builder.Add(Assert(GetToken(dim), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(dim)), desc, builder.Context));
        j++;
      }
      if (allocateArray.ElementInit != null) {
        CheckWellformed(allocateArray.ElementInit, new WFOptions(), locals, builder, etran);
      } else if (allocateArray.InitDisplay != null) {
        var dim = allocateArray.ArrayDimensions[0];
        var desc = new ArrayInitSizeValid(allocateArray, dim);
        builder.Add(Assert(GetToken(dim), Bpl.Expr.Eq(etran.TrExpr(dim), Bpl.Expr.Literal(allocateArray.InitDisplay.Count)), desc, builder.Context));
        foreach (var v in allocateArray.InitDisplay) {
          CheckWellformed(v, new WFOptions(), locals, builder, etran);
        }
      } else if (options.DefiniteAssignmentLevel == 0) {
        // cool
      } else if ((2 <= options.DefiniteAssignmentLevel && options.DefiniteAssignmentLevel != 4) ||
                 options.Get(CommonOptionBag.EnforceDeterminism) ||
                 !allocateArray.ElementType.HasCompilableValue) {
        // this is allowed only if the array size is such that it has no elements
        Bpl.Expr zeroSize = Bpl.Expr.False;
        foreach (Expression dim in allocateArray.ArrayDimensions) {
          zeroSize = BplOr(zeroSize, Bpl.Expr.Eq(Bpl.Expr.Literal(0), etran.TrExpr(dim)));
        }
        var desc = new ArrayInitEmpty(allocateArray.ElementType.ToString(), allocateArray.ArrayDimensions);
        builder.Add(Assert(allocateArray.Origin, zeroSize, desc, builder.Context));
      }

      Bpl.IdentifierExpr nw = GetNewVar_IdExpr(tok, locals);

      SelectAllocateObject(tok, nw, allocateArray.Type, true, builder, etran);
      int i = 0;
      foreach (Expression dim in allocateArray.ArrayDimensions) {
        // assume Array#Length($nw, i) == arraySize;
        Bpl.Expr arrayLength = ArrayLength(tok, nw, allocateArray.ArrayDimensions.Count, i);
        builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(arrayLength, etran.TrExpr(dim))));
        i++;
      }
      if (allocateArray.ElementInit != null) {
        CheckElementInit(tok, true, allocateArray.ArrayDimensions, allocateArray.ElementType, allocateArray.ElementInit, nw, builder, etran, new WFOptions());
      } else if (allocateArray.InitDisplay != null) {
        int ii = 0;
        foreach (var v in allocateArray.InitDisplay) {
          var EE_ii = etran.TrExpr(v);
          // assert EE_ii satisfies any subset-type constraints;
          CheckSubrange(v.Origin, EE_ii, v.Type, allocateArray.ElementType, v, builder);
          // assume nw[ii] == EE_ii;
          var ai = ReadHeap(tok, etran.HeapExpr, nw, GetArrayIndexFieldName(tok, [Bpl.Expr.Literal(ii)]));
          builder.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.Eq(UnboxUnlessInherentlyBoxed(ai, allocateArray.ElementType), AdaptBoxing(tok, EE_ii, v.Type, allocateArray.ElementType))));
          ii++;
        }
      }
      Bpl.Cmd heapAllocationRecorder = null;
      if (codeContext is IteratorDecl) {
        var iter = (IteratorDecl)codeContext;
        // $Heap[this, _new] := Set#UnionOne($Heap[this, _new], $Box($nw));
        var th = new Bpl.IdentifierExpr(tok, etran.This, Predef.RefType);
        var nwField = new Bpl.IdentifierExpr(tok, GetField(iter.Member_New));
        var thisDotNew = ApplyUnbox(tok, ReadHeap(tok, etran.HeapExpr, th, nwField), Predef.SetType);
        var unionOne = FunctionCall(tok, BuiltinFunction.SetUnionOne, Predef.BoxType, thisDotNew, ApplyBox(tok, nw));
        var heapRhs = UpdateHeap(tok, etran.HeapExpr, th, nwField, unionOne);
        heapAllocationRecorder = Bpl.Cmd.SimpleAssign(tok, etran.HeapCastToIdentifierExpr, heapRhs);
      }
      CommitAllocatedObject(tok, nw, heapAllocationRecorder, builder, etran);
      // bLhs := $nw;
      CheckSubrange(tok, nw, allocateArray.Type, rhsTypeConstraint, null, builder);
      return HandleGivenLhs(tok, bGivenLhs, lhsType, builder, stmt, bLhs, nw, allocateArray);
    } else {
      throw new UnreachableException();
    }
  }

  private Expr HandleGivenLhs(IOrigin tok, Bpl.IdentifierExpr bGivenLhs, Type lhsType, BoogieStmtListBuilder builder,
    Statement stmt, Bpl.IdentifierExpr bLhs, Bpl.IdentifierExpr nw, TypeRhs typeRhs) {
    if (bGivenLhs != null) {
      Contract.Assert(bGivenLhs == bLhs);
      // box the RHS, then do the assignment
      var cmd = Bpl.Cmd.SimpleAssign(tok, bGivenLhs, CondApplyBox(tok, nw, typeRhs.Type, lhsType));
      proofDependencies?.AddProofDependencyId(cmd, tok, new AssignmentDependency(stmt.Origin));
      builder.Add(cmd);
      return bGivenLhs;
    } else {
      // do the assignment, then box the result
      var cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, nw);
      proofDependencies?.AddProofDependencyId(cmd, tok, new AssignmentDependency(stmt.Origin));
      builder.Add(cmd);
      return CondApplyBox(tok, bLhs, typeRhs.Type, lhsType);
    }
  }
}