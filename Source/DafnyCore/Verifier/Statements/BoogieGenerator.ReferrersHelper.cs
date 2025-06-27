using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator
{
  private class ReferrersHelper {
    public BoogieGenerator BG { get; }
    public bool VerifyReferrers => BG.VerifyReferrers;
    public Declaration CurrentDeclaration => BG.CurrentDeclaration;

    public ImmutableDictionary<string, (object tracked, Boogie.IdentifierExpr tracker)> DefiniteAssignmentTrackers => BG.DefiniteAssignmentTrackers;
    
    public ReferrersHelper(BoogieGenerator bg) {
      this.BG = bg;
    }

    public void AssumeEmptyFor(Boogie.IdentifierExpr nw, IOrigin tok, BoogieStmtListBuilder builder,
      ExpressionTranslator etran)
    {
      if (VerifyReferrers) {
        // Add assume readReferrers($ReferrersHeap, nw) == Set#Empty()

        builder.Add(
          new AssumeCmd(tok,
            Boogie.Expr.Eq(
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
      if (!VerifyReferrers || m is Lemma || !CountsAsReferrer(i) || !i.Type.MayInvolveReferences) {
        return;
      }
      var localField = i.GetLocalField(m);
      var field = BG.GetField(localField); // Make sure definition is added.
      var tuple = FunctionCall(i.Origin, BG.Predef.Tuple2Constructor.Name, null, 
        BG.FunctionCall(i.Origin, BuiltinFunction.Box, null, Id(i.Origin, "locals")),
        BG.FunctionCall(i.Origin, BuiltinFunction.Box, null, 
          BG.FunctionCall(i.Origin, BuiltinFunction.LocalField, BG.Predef.FieldType,
            Id(i.Origin, field.Name),
            Id(i.Origin, "depth"))));
      var boxedTuple = BG.FunctionCall(i.Origin, BuiltinFunction.Box, null, tuple);
      var isMember = BG.FunctionCall(i.Origin, BuiltinFunction.SetIsMember, null,
        BG.FunctionCall(i.Origin, BuiltinFunction.ReadReferrers, null,
          ordinaryEtran.ReferrersHeapExpr, Id(i.Origin, i.AssignUniqueName(m.IdGenerator))),
        boxedTuple);
      req.Add(BG.FreeRequires(i.Origin, isMember, null));
    }

    public void RemovePreAssign(IOrigin tok, Expression lhs, BoogieStmtListBuilder builder, Variables locals,
      ExpressionTranslator etran) {
      if (!VerifyReferrers || !lhs.Type.MayInvolveReferences || CurrentDeclaration is Lemma) {
        return;
      }

      switch (lhs.Resolved)
      {
        // Havoc the referrersHeap by default, unless we know what to do.
        case IdentifierExpr { Type.IsRefType: true, Var: LocalVariable localVariable }
          when CurrentDeclaration is MethodOrConstructor m:
          RemovePreAssignLocalVar(tok, lhs, localVariable, m, builder, etran);
          return;
        case MemberSelectExpr { Type.IsRefType: true, Obj: var memberObj, Member: Field memberField }:
          RemovePreAssignMemberSelect(builder, locals, etran, tok, memberObj, memberField);
          return;
        default:
          ReferrersNotSupported(builder, etran, tok);
          break;
      }
    }

    private void RemovePreAssignLocalVar(IOrigin tok, Expression lhs,
      LocalVariable localVariable, MethodOrConstructor m, BoogieStmtListBuilder builder,
      ExpressionTranslator etran) {
      if (!CountsAsReferrer(localVariable) || m is Lemma) {
        return;
      }

      var tracker =
        DefiniteAssignmentTrackers.TryGetValue(localVariable.AssignUniqueName(CurrentDeclaration.IdGenerator),
          out var assignmentTracker)
          ? assignmentTracker.tracker
          : null;
      RemovePreAssignField(tok, lhs, localVariable.GetLocalField(m), tracker, builder, etran);
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
      if (!VerifyReferrers || !formal.Type.MayInvolveReferences || !CountsAsReferrer(formal) || method is Lemma) {
        return;
      }

      var field = formal.GetLocalField(method);
      var bField = BG.GetField(field);
      var fieldExpr = BG.FunctionCall(tok, BuiltinFunction.LocalField, BG.Predef.FieldType,
        Id(tok, bField), Boogie.Expr.Add(Id(tok, "depth"), One(tok)));
      var objExpr = BG.Predef.Locals;
      RemoveUnassignAux(tok, bLhs, objExpr, fieldExpr, null, builder, etran);
    }

    private void RemovePreAssignMemberSelect(BoogieStmtListBuilder builder, Variables locals,
      ExpressionTranslator etran, IOrigin tok, Expression memberObj, Field memberField) {
      var oldRhs = locals.GetOrCreate("$oldRhs",
        () => new Boogie.LocalVariable(tok, new Boogie.TypedIdent(tok, "$oldRhs", BG.Predef.RefType)));

      var bLhs = new Boogie.IdentifierExpr(tok, oldRhs);
      var heapRead = BG.ReadHeap(tok, etran.HeapExpr, etran.TrExpr(memberObj), Id(tok, BG.GetField(memberField).Name));
      var unboxedHeapRead = BG.FunctionCall(tok, BuiltinFunction.Unbox, BG.Predef.RefType, heapRead);
      builder.Add(Boogie.Cmd.SimpleAssign(tok, bLhs, unboxedHeapRead));

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
      Expr bCond = Boogie.Expr.Neq(lhs, BG.Predef.Null);
      if (assignTracker != null) {
        bCond = BplAnd(bCond, assignTracker);
      }

      var ifCmd = new Boogie.IfCmd(tok,
        bCond,
        b.Collect(tok),
        null, null);
      builder.Add(ifCmd);
    }

    public void AddPostAssign(IOrigin tok, Expression memloc, Expr rhsVariable, BoogieStmtListBuilder builder,
      ExpressionTranslator etran) {
      if (!VerifyReferrers || !memloc.Type.MayInvolveReferences || BG.CurrentDeclaration is Lemma) {
        return;
      }

      // Havoc the referrersHeap by default, unless we know what to do.
      if (memloc.Resolved is IdentifierExpr { Type.IsRefType: true, Var: LocalVariable { } localVariable }
          && CurrentDeclaration is MethodOrConstructor m) {
        AddPostAssignLocalVar(tok, etran.TrExpr(memloc), builder, etran, localVariable, m, false);
        return;
      }

      if (memloc.Resolved is MemberSelectExpr { Type.IsRefType: true, Obj: var memberObj, Member: Field memberField }) {
        AddPostAssignMemberSelect(tok, rhsVariable, builder, etran, memberObj, memberField);
        return;
      }

      ReferrersNotSupported(builder, etran, tok);
    }

    private void AddPostAssignLocalVar(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, LocalVariable localVariable, MethodOrConstructor m, bool deeperLevel) {
      if (!CountsAsReferrer(localVariable) || m is Lemma) {
        return;
      }

      AddPostAssignField(tok, bRhs, builder, etran, localVariable.GetLocalField(m), deeperLevel);
    }

    public void AddAssignPreCallFormal(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Formal formal, MethodOrConstructor m) {
      if (!VerifyReferrers || !CountsAsReferrer(formal) || !formal.Type.MayInvolveReferences || m is Lemma) {
        return;
      }

      AddPostAssignField(tok, bRhs, builder, etran, formal.GetLocalField(m), true);
    }

    private void AddPostAssignField(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Field field, bool deeperLevel) {
      if (!CountsAsReferrer(field) || !field.Type.MayInvolveReferences) {
        return;
      }

      var bField = BG.GetField(field);
      var depth = Id(tok, "depth");
      if (deeperLevel) {
        depth = Boogie.Expr.Add(depth, One(tok));
      }

      var fieldExpr = BG.FunctionCall(tok, BuiltinFunction.LocalField, BG.Predef.FieldType,
        Id(tok, bField), depth);
      AddPostAssignAux(tok, bRhs, BG.Predef.Locals, fieldExpr, builder, etran);
    }

    private void AddPostAssignMemberSelect(IOrigin tok, Expr bRhs, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, Expression memberObj, Field memberField) {
      if (!CountsAsReferrer(memberField) || !memberField.Type.MayInvolveReferences) {
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
        Boogie.Cmd.SimpleAssign(tok, etran.ReferrerrsHeapCastToIdentifierExpr, referrersHeapRhs);
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

    private void ReferrersNotSupported(BoogieStmtListBuilder builder, ExpressionTranslator etran, IOrigin tok) {
      BG.program.Reporter.Warning(MessageSource.Verifier, "Unknown referrers action", tok,
        "This update statement is not yet supported by referrers..");
      builder.Add(new HavocCmd(tok, [etran.ReferrerrsHeapCastToIdentifierExpr]));
    }
  }
}