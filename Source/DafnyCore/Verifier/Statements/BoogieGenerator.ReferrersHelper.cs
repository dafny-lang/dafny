using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Runtime.CompilerServices;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private class ReferrersHelper {
    private const string IndexfieldInverse = "IndexField_Inverse";
    private const string Indexfield = "IndexField";
    public BoogieGenerator BG { get; }
    public bool VerifyReferrers => BG.VerifyReferrers;
    public Declaration CurrentDeclaration => BG.CurrentDeclaration;

    public ImmutableDictionary<string, (object tracked, Boogie.IdentifierExpr tracker)> DefiniteAssignmentTrackers => BG.DefiniteAssignmentTrackers;

    public ReferrersHelper(BoogieGenerator bg) {
      this.BG = bg;
    }

    public void AssumeEmptyFor(Boogie.IdentifierExpr nw, IOrigin tok, BoogieStmtListBuilder builder,
      ExpressionTranslator etran) {
      if (VerifyReferrers) {
        // Add assume readReferrers($ReferrersHeap, nw) == Set#Empty()

        builder.Add(
          new AssumeCmd(tok,
            Expr.Eq(
              BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, nw),
              BG.FunctionCall(tok, BuiltinFunction.SetEmpty, BG.Predef.SetType)
            )
          ));
      }
    }

    /// <summary>
    /// Generates the following Boogie code:
    /// <code>
    /// free requires Set#IsMember(readReferrers($ReferrersHeap, t#0), 
    ///   $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.ReferrersMethodCall.t, depth)))));
    /// </code>
    /// </summary>
    public void AddFreeRequires(Formal i, MethodOrConstructor m, ExpressionTranslator ordinaryEtran, List<Boogie.Requires> req) {
      if (!VerifyReferrers || m.IsGhost || !CountsAsReferrer(i) || !i.Type.MayInvolveReferences) {
        return;
      }

      var localField = i.GetLocalField(m);
      var field = BG.GetField(localField); // Make sure definition is added.
      var tok = i.Origin;
      if (!i.Type.IsRefType) {
        BG.program.Reporter.Warning(MessageSource.Verifier, "Unknown formal referrers", tok,
          $"This formal is not supported yet in --referrers because it might contain references but is not a reference itself.");
        return;
      }
      var boxedTuple = BoxedLocalVariableAtCurrentDepth(tok, field);
      var isMember = BG.FunctionCall(i.Origin, BuiltinFunction.SetIsMember, null,
        BG.FunctionCall(i.Origin, BuiltinFunction.ReadReferrers, null,
          ordinaryEtran.ReferrersHeapExpr, Id(i.Origin, i.AssignUniqueName(m.IdGenerator))),
        boxedTuple);
      req.Add(BG.FreeRequires(i.Origin, isMember, null));
    }

    private NAryExpr BoxedLocalVariableAtCurrentDepth(IOrigin tok, Constant field) {
      return BG.Box(tok, FunctionCall(tok, BG.Predef.Tuple2Constructor.Name, null,
        BG.FunctionCall(tok, BuiltinFunction.Box, null, Id(tok, "locals")),
        BG.Box(tok,
          BG.FunctionCall(tok, BuiltinFunction.LocalField, BG.Predef.FieldType,
            Id(tok, field.Name),
            Id(tok, "depth")))));
    }

    public void UnassignLocalVariables(IOrigin tok, Variables locals,
      BoogieStmtListBuilder builder,
      ExpressionTranslator etran,
      ImmutableDictionary<string, (object tracked, Boogie.IdentifierExpr tracker)> assignmentTrackers) {
      foreach (var trackedLocalVariable in assignmentTrackers) {
        var localVar = trackedLocalVariable.Value.tracked;
        if (localVar is LocalVariable l) {
          // Need to unassign
          var lhs = new IdentifierExpr(tok, l);
          RemovePreAssign(tok, lhs, builder, locals, etran);
        }
        /*
         Example:
         if (defass#t_local#0 && t_local#0 != null) {
          $ReferrersHeap := updateReferrers($ReferrersHeap, t_local#0, Set#Difference(readReferrers($ReferrersHeap, t_local#0),
            Set#UnionOne(Set#Empty(),
            $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(_module.__default.EnsuresReferrersUnchanged.t__local, depth))))
          )));
        */
      }
    }

    public void RemovePreAssign(IOrigin tok, Expression lhs, BoogieStmtListBuilder builder, Variables locals,
      ExpressionTranslator etran) {
      if (!VerifyReferrers || !lhs.Type.MayInvolveReferences || CurrentDeclaration is Lemma or MethodOrConstructor { IsGhost: true }) {
        return;
      }

      switch (lhs.Resolved) {
        // Havoc the referrersHeap by default, unless we know what to do.
        case IdentifierExpr { Var: LocalVariable localVariable }
          when CurrentDeclaration is MethodOrConstructor m:
          RemovePreAssignLocalVar(tok, lhs, localVariable, m, builder, etran);
          return;
        case IdentifierExpr { Var: Formal outFormal }
          when CurrentDeclaration is MethodOrConstructor m:
          RemovePreAssignOutFormal(tok, lhs, outFormal, m, builder, etran);
          return;
        case MemberSelectExpr { Obj: var memberObj, Member: Field memberField }:
          RemovePreAssignMemberSelect(builder, locals, etran, tok, memberObj, memberField);
          return;
        default:
          ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{lhs} is not a variable or member assignment of a reference type");
          break;
      }
    }

    private void RemovePreAssignLocalVar(IOrigin tok, Expression lhs,
      LocalVariable localVariable, MethodOrConstructor m, BoogieStmtListBuilder builder,
      ExpressionTranslator etran) {
      if (!CountsAsReferrer(localVariable) || m.IsGhost) {
        return;
      }
      if (!lhs.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{lhs} might involve references but is not a reference type");
        return;
      }

      var tracker =
        DefiniteAssignmentTrackers.TryGetValue(localVariable.AssignUniqueName(CurrentDeclaration.IdGenerator),
          out var assignmentTracker)
          ? assignmentTracker.tracker
          : null;
      RemovePreAssignField(tok, lhs, localVariable.GetLocalField(m), tracker, builder, etran);
    }
    
    private void RemovePreAssignOutFormal(IOrigin tok, Expression lhs, Formal outFormal,
      MethodOrConstructor m, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      if (!CountsAsReferrer(outFormal) || m.IsGhost) {
        return;
      }
      if (!lhs.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{lhs} might involve references but is not a reference type");
        return;
      }

      var tracker =
        DefiniteAssignmentTrackers.TryGetValue(outFormal.AssignUniqueName(CurrentDeclaration.IdGenerator),
          out var assignmentTracker)
          ? assignmentTracker.tracker
          : null;
      RemovePreAssignField(tok, lhs, outFormal.GetLocalField(m), tracker, builder, etran);
    }

    private void RemovePreAssignField(IOrigin tok,
      Expression lhs,
      Field field, Boogie.IdentifierExpr tracker,
      BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      var bField = BG.GetField(field);
      var fieldExpr = BG.FunctionCall(tok, BuiltinFunction.LocalField, BG.Predef.FieldType,
        Id(tok, bField), Id(tok, "depth"));
      Expr bLhs = etran.TrExpr(lhs);
      var objExpr = BG.Predef.Locals;
      RemoveUnassignAux(tok, bLhs, objExpr, fieldExpr, tracker, builder, etran);
    }

    public void RemovePostCallFormal(IOrigin tok, Expr bLhs, Formal formal,
      MethodOrConstructor method,
      BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      if (!VerifyReferrers || !formal.Type.MayInvolveReferences || !CountsAsReferrer(formal) || method.IsGhost) {
        return;
      }
      if (!formal.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{formal} might involve references but is not a reference type");
        return;
      }

      var field = formal.GetLocalField(method);
      var bField = BG.GetField(field);
      var fieldExpr = BG.FunctionCall(tok, BuiltinFunction.LocalField, BG.Predef.FieldType,
        Id(tok, bField), Expr.Add(Id(tok, "depth"), One(tok)));
      var objExpr = BG.Predef.Locals;
      RemoveUnassignAux(tok, bLhs, objExpr, fieldExpr, null, builder, etran);
    }

    private void RemovePreAssignMemberSelect(BoogieStmtListBuilder builder, Variables locals,
      ExpressionTranslator etran, IOrigin tok, Expression memberObj, Field memberField) {
      if (!memberField.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{memberField} might involve references but is not a reference type");
        return;
      }
      var oldRhs = locals.GetOrCreate("$oldRhs",
        () => new Boogie.LocalVariable(tok, new TypedIdent(tok, "$oldRhs", BG.Predef.RefType)));

      var bLhs = new Boogie.IdentifierExpr(tok, oldRhs);
      var heapRead = BG.ReadHeap(tok, etran.HeapExpr, etran.TrExpr(memberObj), Id(tok, BG.GetField(memberField).Name));
      var unboxedHeapRead = BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType, heapRead);
      builder.Add(Cmd.SimpleAssign(tok, bLhs, unboxedHeapRead));

      var fieldId = Id(tok, BG.GetField(memberField).Name);
      var objExpr = etran.TrExpr(memberObj);
      var useSurrogateLocal = BG.inBodyInitContext && Expression.AsThis(memberObj) != null;
      var nm = BG.SurrogateName(memberField);
      var tracker = BG.DefiniteAssignmentTrackers.TryGetValue(nm, out var trackedTracker) ? trackedTracker.tracker : null;
      RemoveUnassignAux(tok, bLhs, objExpr, fieldId, tracker, builder, etran);
    }

    /// <summary>
    /// Generates boogie code like the following. The initialization tracker, if null, assumes the variable to be already initialized.
    /// <code>
    /// if (lhs != null && assignTracker) {
    ///   assume Set#IsMember(readReferrers($ReferrersHeap, bLhs), $Box(#_System._tuple#2._#Make2($Box(objExpr), $Box(fieldId))));
    ///   $ReferrersHeap := updateReferrers($ReferrersHeap, lhs, Set#Difference(readReferrers($ReferrersHeap, bLhs), Set#UnionOne(Set#Empty(), $Box(#_System._tuple#2._#Make2($Box(objExpr),  /// $Box(fieldId))))
    ///   ));
    /// }
    /// </code>
    /// </summary>
    private void RemoveUnassignAux(IOrigin tok, Expr lhs, Expr objExpr, Expr fieldExpr,
      Boogie.IdentifierExpr assignTracker, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      var obj = BG.ApplyBox(tok, objExpr);
      var f = BG.ApplyBox(tok, fieldExpr);
      var memlocExpr = FunctionCall(tok, BG.Predef.Tuple2Constructor.Name, BG.Predef.DatatypeType, obj, f);
      var tupleBoxObjAndField = BG.ApplyBox(tok, memlocExpr);
      var referrersHeapRhs = BG.UpdateReferrersHeap(tok, etran.ReferrersHeapExpr,
        lhs, BG.FunctionCall(
          tok, BuiltinFunction.SetDifference,
          BG.Predef.SetType,
          BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, lhs),
          BG.FunctionCall(tok, BuiltinFunction.SetUnionOne, BG.Predef.SetType,
            BG.FunctionCall(tok, BuiltinFunction.SetEmpty, BG.Predef.SetType),
            tupleBoxObjAndField
          )));
      var preReferrerHeapUpdate =
        Cmd.SimpleAssign(tok, etran.ReferrerrsHeapCastToIdentifierExpr, referrersHeapRhs);
      var b = new StmtListBuilder();
      b.Add(new AssumeCmd(tok,
        BG.FunctionCall(tok, BuiltinFunction.SetIsMember, BG.Predef.BoxType,
          BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, lhs),
          tupleBoxObjAndField
        )
      ));
      b.Add(preReferrerHeapUpdate);
      Expr bCond = Expr.Neq(lhs, BG.Predef.Null);
      if (assignTracker != null) {
        bCond = BplAnd(bCond, assignTracker);
      }

      var ifCmd = new IfCmd(tok,
        bCond,
        b.Collect(tok),
        null, null);
      builder.Add(ifCmd);
    }

    public void AddPostAssign(IOrigin tok, Expression memloc, Expr rhsVariable, BoogieStmtListBuilder builder,
      ExpressionTranslator etran) {
      if (!VerifyReferrers || !memloc.Type.MayInvolveReferences) {
        return;
      }

      switch (memloc.Resolved) {
        // Havoc the referrersHeap by default, unless we know what to do.
        case IdentifierExpr { Var: LocalVariable { } localVariable }
          when CurrentDeclaration is MethodOrConstructor m:
          AddPostAssignLocalVar(tok, etran.TrExpr(memloc), builder, etran, localVariable, m, false);
          return;
        case IdentifierExpr { Var: Formal { } outFormal }
          when CurrentDeclaration is MethodOrConstructor m:
          AddPostAssignOutFormal(tok, etran.TrExpr(memloc), builder, etran, outFormal, m, false);
          return;
        case MemberSelectExpr { Obj: var memberObj, Member: Field memberField }:
          AddPostAssignMemberSelect(tok, rhsVariable, builder, etran, memberObj, memberField);
          return;
        default:
          ReferrersNotSupportedHavocFallback(builder, etran, tok, "the lhs is not a simple a := ... or a.b := ...");
          break;
      }
    }

    private void AddPostAssignLocalVar(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, LocalVariable localVariable, MethodOrConstructor m, bool deeperLevel) {
      if (!CountsAsReferrer(localVariable)) {
        return;
      }

      AddPostAssignField(tok, bRhs, builder, etran, localVariable.GetLocalField(m), deeperLevel);
    }
    
    private void AddPostAssignOutFormal(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Formal formal, MethodOrConstructor m, bool deeperLevel) {
      if (!CountsAsReferrer(formal) || m.IsGhost) {
        return;
      }

      AddPostAssignField(tok, bRhs, builder, etran, formal.GetLocalField(m), deeperLevel);
    }

    public void AddAssignPreCallFormal(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Formal formal, MethodOrConstructor m) {
      if (!VerifyReferrers || !CountsAsReferrer(formal) || !formal.Type.MayInvolveReferences || m.IsGhost) {
        return;
      }

      if (!formal.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{formal} might involve references but is not a reference type");
        return;
      }

      AddPostAssignField(tok, bRhs, builder, etran, formal.GetLocalField(m), true);
    }

    private void AddPostAssignField(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Field field, bool deeperLevel) {
      if (!field.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{field} might involve references but is not a reference type");
        return;
      }

      var bField = BG.GetField(field);
      Boogie.Expr depth = Id(tok, "depth");
      if (deeperLevel) {
        depth = Expr.Add(depth, One(tok));
      }

      var fieldExpr = BG.FunctionCall(tok, BuiltinFunction.LocalField, BG.Predef.FieldType,
        Id(tok, bField), depth);
      AddPostAssignAux(tok, bRhs, BG.Predef.Locals, fieldExpr, builder, etran);
    }

    private void AddPostAssignMemberSelect(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Expression memberObj, Field memberField) {
      if (!CountsAsReferrer(memberField)) {
        return;
      }
      if (!memberField.Type.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, $"{memberField} might involve references but is not a reference type");
        return;
      }

      var objExpr = etran.TrExpr(memberObj);
      var fieldId = Id(tok, BG.GetField(memberField).Name);

      AddPostAssignAux(tok, bRhs, objExpr, fieldId, builder, etran);
    }


    /// <summary>
    /// Adds the following Boogie code to the builder
    ///
    /// <code>
    /// if (bRhs != null) {
    ///   assume !Set#IsMember(readReferrers($ReferrersHeap, bRhs), $Box(#_System._tuple#2._#Make2($Box(objExpr), $Box(fieldExpr))));
    ///   $ReferrersHeap := updateReferrers($ReferrersHeap, bRhs, Set#UnionOne(readReferrers($ReferrersHeap, bRhs),
    ///     $Box(#_System._tuple#2._#Make2($Box(objExpr), $Box(fieldExpr)))
    ///   ));
    /// }
    /// </code>
    /// </summary>
    private void AddPostAssignAux(IOrigin tok, Expr bRhs, Expr objExpr, Expr fieldExpr,
      BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      var obj = BG.ApplyBox(tok, objExpr);
      var f = BG.ApplyBox(tok, fieldExpr);
      var memLocExpr = FunctionCall(tok, BG.Predef.Tuple2Constructor.Name, BG.Predef.DatatypeType, obj, f);
      var memLocExprBox = BG.ApplyBox(tok, memLocExpr);
      var referrersHeapRhs = BG.UpdateReferrersHeap(tok, etran.ReferrersHeapExpr,
        bRhs, BG.FunctionCall(
          tok, BuiltinFunction.SetUnionOne,
          BG.Predef.SetType,
          BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, bRhs),
          memLocExprBox
        ));
      var postReferrersHeapUpdate =
        Cmd.SimpleAssign(tok, etran.ReferrerrsHeapCastToIdentifierExpr, referrersHeapRhs);
      var b = new StmtListBuilder();
      b.Add(new AssumeCmd(tok,
        Expr.Not(
          BG.FunctionCall(tok, BuiltinFunction.SetIsMember, BG.Predef.BoxType,
            BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, bRhs),
            memLocExprBox
          )
        )
      ));
      b.Add(postReferrersHeapUpdate);
      var ifCmd = new IfCmd(tok,
        Expr.Neq(bRhs, BG.Predef.Null),
        b.Collect(tok),
        null, null);
      builder.Add(ifCmd);
    }

    private static bool CountsAsReferrer(LocalVariable localVariable) {
      return !localVariable.IsGhost || localVariable.HasUserAttribute(TrackingAttribute, out _);
    }

    private bool CountsAsReferrer(Formal formal) {
      return !formal.IsGhost;
    }

    public bool CountsAsReferrer(Field field) {
      return !field.IsGhost || field.HasUserAttribute(TrackingAttribute, out _);
    }

    private void ReferrersNotSupportedHavocFallback(BoogieStmtListBuilder builder, ExpressionTranslator etran, IOrigin tok, string reason) {
      WarningReferrersNotSupportOnUpdateStmt(tok, reason);
      builder.Add(new HavocCmd(tok, [etran.ReferrerrsHeapCastToIdentifierExpr]));
    }

    private void WarningReferrersNotSupportOnUpdateStmt(IOrigin tok, string reason) {
      BG.program.Reporter.Warning(MessageSource.Verifier, "Unknown referrers action", tok,
        $"This update statement is not yet supported by referrers because {reason}.");
    }

    /// <summary>
    /// Generates the equivalent of
    /// <code>
    /// assume readReferrers($ReferrersHeap, this) ==  Set#UnionOne(Set#Empty(),
    /// $Box(#_System._tuple#2._#Make2($Box(locals), $Box(local_field(constructorName.this, depth))))
    /// );
    /// </code>
    /// </summary>
    public void AssumeThisFresh(Constructor constructor, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      if (!VerifyReferrers) {
        return;
      }

      var tok = constructor.Origin;
      var thisField = BG.GetField(constructor.GetThisFormal().GetLocalField(constructor));
      var assumeCmd = new AssumeCmd(
        tok,
        BG.FunctionCall(
          tok,
          BuiltinFunction.SetEqual,
          null,
          BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, Id(tok, "this")),
          BG.FunctionCall(
            tok,
            BuiltinFunction.SetUnionOne,
            BG.Predef.SetType,
            BG.FunctionCall(
              tok,
              BuiltinFunction.SetEmpty,
              BG.Predef.SetType
            ),
            BoxedLocalVariableAtCurrentDepth(tok, thisField)
          )
        )
      );
      builder.Add(assumeCmd);
    }

    public void AddArrayInitReferrer(IOrigin tok,
      Variables locals, Expression init, List<Variable> bvs, Trigger tr,
      Expr ante,
      Expr arrayAtIndex,
      Expr arrayIndexFieldName,
      List<Expr> bDims,
      Boogie.IdentifierExpr nw,
      BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      if (!VerifyReferrers) {
        return;
      }
      // For n-dimensional with n > 1, return not supported
      if (bvs.Count != 1 || bDims.Count != 1) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, "the dimension is not 1");
        return;
      }

      // If the lambda init expression does not return a reference, not supported yet.
      if (init.Type.NormalizeExpand() is not ArrowType arrowType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, "the initialization is not a lambda");
        return;
      }

      if (!arrowType.Result.MayInvolveReferences) {
        return; // No need of referrers
      }

      if (!arrowType.Result.IsRefType) {
        ReferrersNotSupportedHavocFallback(builder, etran, tok, "the output of the lambda might involve references but it's not a reference");
        return; // No need of referrers
      }

      /*$OldReferrersHeap := $ReferrersHeap;
        havoc $ReferrersHeap; */
      var oldReferrersHeap = locals.GetOrCreate("$OldReferrersHeap",
        () => new Boogie.LocalVariable(tok, new TypedIdent(tok, "$OldReferrersHeap", BG.Predef.ReferrersHeapType)));
      builder.Add(Cmd.SimpleAssign(tok,
        new Boogie.IdentifierExpr(tok, oldReferrersHeap),
        etran.ReferrersHeapExpr));
      builder.Add(new HavocCmd(tok, [etran.ReferrerrsHeapCastToIdentifierExpr]));

      // All objects except the ones stored in the array have their referrers unchanged.
      /*
      assume (forall $o: ref ::
        { readReferrers($ReferrersHeap, $o) }
(forall bvs :: { tr } ante ==> $o != $Unbox(read($Heap, $nw, arrayIndexFieldName): ref))
        ==> 
        readReferrers($ReferrersHeap, $o) == readReferrers($OldReferrersHeap, $o));*/
      var forallVars = new List<Variable>();
      var o = new BoundVariable(tok, new TypedIdent(tok, "$o", BG.Predef.RefType));
      forallVars.Add(o);
      var trigger = new Trigger(tok, true, [BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, Id(tok, "$o"))]);

      var innerForall = new Boogie.ForallExpr(tok, bvs, tr,
        Expr.Imp(ante,
          Expr.Neq(Id(tok, "$o"), BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType,
            BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName)))));

      var equality = Expr.Eq(
        BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, Id(tok, "$o")),
        BG.ReadReferrersHeap(tok, new Boogie.IdentifierExpr(tok, oldReferrersHeap), Id(tok, "$o")));

      var outerForall = new Boogie.ForallExpr(tok, forallVars, trigger,
        Expr.Imp(innerForall, equality));

      builder.Add(new AssumeCmd(tok, outerForall));

      // For all objects in the array, the referrers before is a subset of the referrers after
      /*
      assume (forall bvs ::
        { tr }
        ante
        ==>
        Set#Subset(
          readReferrers($OldReferrersHeap, $Unbox(read($Heap, $nw, arrayIndexFieldName)): ref),
          readReferrers($ReferrersHeap, $Unbox(read($Heap, $nw, arrayIndexFieldName)): ref)
        )
      );*/
      var forallExpr = new Boogie.ForallExpr(tok, bvs, tr,
        Expr.Imp(ante,
          BG.FunctionCall(tok, BuiltinFunction.SetSubset, null,
            BG.ReadReferrersHeap(tok, new Boogie.IdentifierExpr(tok, oldReferrersHeap),
              BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType,
                BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName))),
            BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr,
              BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType,
                BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName))))));

      builder.Add(new AssumeCmd(tok, forallExpr));

      // For all objects in the array post-state, their referrers previously did not contain any memory locations from the new array. That makes it possible to consider all memory locations
      // as fresh
      /*
        assume (forall bvs, $r: Box :: 
      { Set#IsMember(readReferrers($OldReferrersHeap, $Unbox(read($Heap, $nw, arrayIndexFieldName)): ref),
         $r) } 
      ante
      && Set#IsMember(readReferrers($OldReferrersHeap, $Unbox(read($Heap, $nw, arrayIndexFieldName)): ref),
         $r)
         ==> $Unbox(_System.Tuple2._0($Unbox($r): DatatypeType)): ref != $nw);*/
      var rVar = new BoundVariable(tok, new TypedIdent(tok, "$r", BG.Predef.BoxType));
      forallVars = [.. bvs, rVar];
      var setIsMember = BG.FunctionCall(tok, BuiltinFunction.SetIsMember, null,
        BG.ReadReferrersHeap(tok, new Boogie.IdentifierExpr(tok, oldReferrersHeap),
          BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType,
            BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName))),
        Id(tok, "$r"));
      // _System.Tuple2._0($Unbox($r): DatatypeType)
      var objectOfR = FunctionCall(tok, BG.Predef.Tuple2Destructors0.Name, BG.Predef.DatatypeType,
        BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.DatatypeType, Id(tok, "$r")));
      var forallExpr1 = new Boogie.ForallExpr(tok, forallVars,
        new Trigger(tok, true, [
          setIsMember
        ]),
        Expr.Imp(
          Expr.And(
            ante,
            setIsMember),
            Expr.Neq(
              BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType,
                objectOfR),
              nw
            )
          )
        );
      builder.Add(new AssumeCmd(tok, forallExpr1));

      // For all objects in the array at index i, the difference of its referrers after minus referrers before contains (nw, i)
      /*assume (forall bvs ::
        { tr }
        { #_System._tuple#2._#Make2($Box($nw), $Box(arrayAtIndex)) }
        ante
        ==>
        Set#IsMember(
          Set#Difference(
            readReferrers($ReferrersHeap, $Unbox(arrayAtIndex): ref),
            readReferrers($OldReferrersHeap, $Unbox(arrayAtIndex): ref)
          ),
          $Box(#_System._tuple#2._#Make2($Box($nw), $Box(arrayAtIndex)))
        )
      );*/
      var tuple2 = FunctionCall(tok, BG.Predef.Tuple2Constructor.Name, BG.Predef.DatatypeType,
        BG.Box(tok, nw),
        BG.Box(tok, arrayIndexFieldName));
      var forallExpr2 = new Boogie.ForallExpr(tok, bvs,
        new Trigger(tok, true, [
          BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName),
        ], new Trigger(tok, true, [tuple2])),
        Expr.Imp(ante,
          BG.FunctionCall(tok, BuiltinFunction.SetIsMember, null,
            BG.FunctionCall(tok, BuiltinFunction.SetDifference, null,
              BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr,
                BG.ApplyUnbox(tok, BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName), BG.Predef.RefType)),
              BG.ReadReferrersHeap(tok, Id(tok, oldReferrersHeap),
                BG.ApplyUnbox(tok, BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName), BG.Predef.RefType))),
            BG.Box(tok, tuple2))));

      builder.Add(new AssumeCmd(tok, forallExpr2));

      // Any new referrer's object must be the array
      // and any new referrer's field must be an index that is equal to the object.
      // That works only for one dimensional arrays for now
      /*assume (forall bvs, $r: Box ::
        { Set#IsMember(readReferrers($ReferrersHeap, $Unbox(arrayIndexAt): ref), $r) }
        ante &&
        Set#IsMember(
          Set#Difference(
            readReferrers($ReferrersHeap, $Unbox(arrayIndexFieldName): ref),
            readReferrers($OldReferrersHeap, $Unbox(arrayIndexFieldName): ref)
          ),
          $r
        )
        ==>
        $Unbox(_System.Tuple2._0($Unbox($r): DatatypeType)): ref == $nw
        && FDim($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field) == 1
        && 0 <= IndexField_Inverse($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field)
        && IndexField_Inverse($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field) < bDim[1]
        && read($Heap, $nw, $Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field))
           == read($Heap, $nw, arrayIndexFieldName)
      );
         */
      var newReferrers = BG.ReadReferrersHeap(tok, etran.ReferrersHeapExpr, arrayAtIndex);
      var setDiff = BG.FunctionCall(tok, BuiltinFunction.SetDifference, null,
        newReferrers,
        BG.ReadReferrersHeap(tok, Id(tok, oldReferrersHeap), arrayAtIndex));

      var rId = Id(tok, rVar);
      var setMember = BG.FunctionCall(tok, BuiltinFunction.SetIsMember, null,
        setDiff, rId);
      var setMemberTrigger = BG.FunctionCall(tok, BuiltinFunction.SetIsMember, null, newReferrers, rId);

      trigger = new Trigger(tok, true, [setMemberTrigger]);

      var tuple2Type = BG.Predef.DatatypeType; // Assuming this is the correct type for tuples

      var unboxedR = BG.ApplyUnbox(tok, rId, tuple2Type);
      var tuple0 = FunctionCall(tok, BG.Predef.Tuple2Destructors0.Name, null, unboxedR);
      var tuple1 = FunctionCall(tok, BG.Predef.Tuple2Destructors1.Name, null, unboxedR);
      tuple0.Type = BG.Predef.BoxType;
      tuple1.Type = BG.Predef.BoxType;
      var condition = Expr.And(
        ante,
        setMember
      );
      
      // FDim($Unbox(_System.Tuple2._1($Unbox($r): DatatypeType)): Field) == 1
      var fdimEq = Expr.Eq(
        FunctionCall(tok, BG.Predef.FieldDimension.Name, Boogie.Type.Int, BG.ApplyUnbox(tok, tuple1, BG.Predef.FieldType)),
         Boogie.Expr.Literal(1));

      var consequence = Expr.And(
        Expr.Eq(BG.ApplyUnbox(tok, tuple0, BG.Predef.RefType), nw),
        Expr.And(
              fdimEq,
              
          Expr.And(
          Expr.Le(Expr.Literal(0),
            FunctionCall(tok, IndexfieldInverse, null, BG.ApplyUnbox(tok, tuple1, BG.Predef.FieldType))),
          Expr.And(
            Expr.Lt(
              FunctionCall(tok, IndexfieldInverse, null, BG.ApplyUnbox(tok, tuple1, BG.Predef.FieldType)),
              bDims[0]),
              Expr.Eq(
                BG.ReadHeap(tok, etran.HeapExpr, nw, BG.ApplyUnbox(tok, tuple1, BG.Predef.FieldType)),
                BG.ReadHeap(tok, etran.HeapExpr, nw, arrayIndexFieldName))
          )
        )
      ));

      forallExpr = new Boogie.ForallExpr(tok, forallVars, trigger, Expr.Imp(condition, consequence));

      builder.Add(new AssumeCmd(tok, forallExpr));

    }
  }
}