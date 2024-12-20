//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
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

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {
    void AddIteratorSpecAndBody(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(iter);
      IsAllocContext = new IsAllocContext(options, false);

      // wellformedness check for method specification
      Bpl.Procedure proc = AddIteratorProc(iter, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);
      if (InVerificationScope(iter)) {
        AddIteratorWellformednessCheck(iter, proc);
      }
      // the method itself
      if (iter.Body != null && InVerificationScope(iter)) {
        proc = AddIteratorProc(iter, MethodTranslationKind.Implementation);
        sink.AddTopLevelDeclaration(proc);
        // ...and its implementation
        AddIteratorImpl(iter, proc);
      }
      this.fuelContext = oldFuelContext;
      IsAllocContext = null;
    }


    Bpl.Procedure AddIteratorProc(IteratorDecl iter, MethodTranslationKind kind) {
      Contract.Requires(iter != null);
      Contract.Requires(kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation);
      Contract.Requires(Predef != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);
      Contract.Ensures(Contract.Result<Bpl.Procedure>() != null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(iter.FullDafnyName, kind), iter);
      currentModule = iter.EnclosingModuleDefinition;
      codeContext = iter;

      var etran = new ExpressionTranslator(this, Predef, iter.Tok, iter);

      var inParams = new List<Bpl.Variable>();
      GenerateMethodParametersChoose(iter.Tok, iter, kind,
        true, true, false, etran, inParams, out var outParams);

      var req = new List<Bpl.Requires>();
      var mod = new List<Bpl.IdentifierExpr>();
      var ens = new List<Bpl.Ensures>();
      // FREE PRECONDITIONS
      if (kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation) {  // the other cases have no need for a free precondition
        // free requires mh == ModuleContextHeight && fh = FunctionContextHeight;
        req.Add(Requires(iter.Tok, true, null, etran.HeightContext(iter), null, null, null));
      }
      mod.Add(etran.HeapCastToIdentifierExpr);

      if (kind != MethodTranslationKind.SpecWellformedness) {
        // USER-DEFINED SPECIFICATIONS
        var comment = "user-defined preconditions";
        foreach (var p in iter.Requires) {
          var (errorMessage, successMessage) = CustomErrorMessage(p.Attributes);
          if (p.Label != null && kind == MethodTranslationKind.Implementation) {
            // don't include this precondition here, but record it for later use
            p.Label.E = etran.Old.TrExpr(p.E);
          } else {
            foreach (var split in TrSplitExprForMethodSpec(new BodyTranslationContext(false), p.E, etran, kind)) {
              if (kind == MethodTranslationKind.Call && split.Tok.IsInherited(currentModule)) {
                // this precondition was inherited into this module, so just ignore it
              } else {
                req.Add(Requires(split.Tok, split.IsOnlyFree, p.E, split.E, errorMessage, successMessage, comment));
                comment = null;
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
        }
        comment = "user-defined postconditions";
        foreach (var p in iter.Ensures) {
          foreach (var split in TrSplitExprForMethodSpec(new BodyTranslationContext(false), p.E, etran, kind)) {
            if (kind == MethodTranslationKind.Implementation && split.Tok.IsInherited(currentModule)) {
              // this postcondition was inherited into this module, so just ignore it
            } else {
              ens.Add(Ensures(split.Tok, split.IsOnlyFree, p.E, split.E, null, null, comment));
              comment = null;
            }
          }
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(iter.Tok, iter.Modifies.Expressions, false, iter.AllowsAllocation, etran.Old, etran, etran.Old)) {
          ens.Add(Ensures(tri.tok, tri.IsFree, null, tri.Expr, tri.ErrorMessage, tri.SuccessMessage, tri.Comment));
        }
      }

      var name = MethodName(iter, kind);
      var proc = new Bpl.Procedure(iter.Tok, name, new List<Bpl.TypeVariable>(),
        inParams, outParams.Values.ToList(), false, req, mod, ens, etran.TrAttributes(iter.Attributes, null));
      AddVerboseNameAttribute(proc, iter.FullDafnyName, kind);

      currentModule = null;
      codeContext = null;

      return proc;
    }

    void AddIteratorWellformednessCheck(IteratorDecl iter, Procedure proc) {
      Contract.Requires(iter != null);
      Contract.Requires(proc != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);

      proofDependencies.SetCurrentDefinition(proc.VerboseName, iter);
      currentModule = iter.EnclosingModuleDefinition;
      codeContext = iter;

      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Contract.Assert(1 <= inParams.Count);  // there should at least be a receiver parameter
      Contract.Assert(proc.OutParams.Count == 0);

      var builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(false));
      var etran = new ExpressionTranslator(this, Predef, iter.Tok, iter);
      // Don't do reads checks since iterator reads clauses mean something else.
      // See comment inside GenerateIteratorImplPrelude().
      etran = etran.WithReadsFrame(null);
      var localVariables = new Variables();
      GenerateIteratorImplPrelude(iter, inParams, new List<Variable>(), builder, localVariables, etran);

      // check well-formedness of any default-value expressions (before assuming preconditions)
      foreach (var formal in iter.Ins.Where(formal => formal.DefaultValue != null)) {
        var e = formal.DefaultValue;
        CheckWellformed(e, new WFOptions(null, false, false, true), localVariables, builder, etran.WithReadsFrame(etran.readsFrame, null));
        builder.Add(new Bpl.AssumeCmd(e.Tok, etran.CanCallAssumption(e)));
        CheckSubrange(e.Tok, etran.TrExpr(e), e.Type, formal.Type, e, builder);
      }
      // check well-formedness of the preconditions, and then assume each one of them
      var wfOptions = new WFOptions();
      foreach (var p in iter.Requires) {
        CheckWellformedAndAssume(p.E, wfOptions, localVariables, builder, etran, "iterator requires clause");
      }
      // check well-formedness of the modifies and reads clauses
      CheckFrameWellFormed(wfOptions, iter.Modifies.Expressions, localVariables, builder, etran);
      CheckFrameWellFormed(wfOptions, iter.Reads.Expressions, localVariables, builder, etran);
      // check well-formedness of the decreases clauses
      foreach (var p in iter.Decreases.Expressions) {
        CheckWellformed(p, wfOptions, localVariables, builder, etran);
      }

      // Next, we assume about this.* whatever we said that the iterator constructor promises
      foreach (var p in iter.Member_Init.Ens) {
        builder.Add(TrAssumeCmdWithDependencies(etran, p.E.Tok, p.E, "iterator ensures clause"));
      }

      // play havoc with the heap, except at the locations prescribed by (this._reads - this._modifies - {this})
      var th = new ThisExpr(iter);  // resolve here
      var rds = new MemberSelectExpr(iter.Tok, th, iter.Member_Reads);
      var mod = new MemberSelectExpr(iter.Tok, th, iter.Member_Modifies);
      builder.Add(Call(builder.Context, iter.Tok, "$IterHavoc0",
        new List<Expr>() { etran.TrExpr(th), etran.TrExpr(rds), etran.TrExpr(mod) },
        new List<Bpl.IdentifierExpr>()));

      // assume the automatic yield-requires precondition (which is always well-formed):  this.Valid()
      var validCall = new FunctionCallExpr(iter.Tok, new Name("Valid"), th, iter.Tok, Token.NoToken, new List<Expression>());
      validCall.Function = iter.Member_Valid;  // resolve here
      validCall.Type = Type.Bool;  // resolve here
      validCall.TypeApplication_AtEnclosingClass = iter.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));  // resolve here
      validCall.TypeApplication_JustFunction = new List<Type>(); // resolved here

      builder.Add(TrAssumeCmd(iter.Tok, etran.TrExpr(validCall)));

      // check well-formedness of the user-defined part of the yield-requires
      foreach (var p in iter.YieldRequires) {
        CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, builder, etran, "iterator yield-requires clause");
      }

      // save the heap (representing the state where yield-requires holds):  $_OldIterHeap := Heap;
      var oldIterHeap = localVariables.GetOrAdd(new Bpl.LocalVariable(iter.Tok, new Bpl.TypedIdent(iter.Tok, "$_OldIterHeap", Predef.HeapType)));
      builder.Add(Bpl.Cmd.SimpleAssign(iter.Tok, new Bpl.IdentifierExpr(iter.Tok, oldIterHeap), etran.HeapExpr));
      // simulate a modifies this, this._modifies, this._new;
      var nw = new MemberSelectExpr(iter.Tok, th, iter.Member_New);
      builder.Add(Call(builder.Context, iter.Tok, "$IterHavoc1",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(mod), etran.TrExpr(nw) },
        new List<Bpl.IdentifierExpr>()));
      // assume the implicit postconditions promised by MoveNext:
      // assume fresh(_new - old(_new));
      var yeEtran = new ExpressionTranslator(this, Predef, etran.HeapExpr, new Bpl.IdentifierExpr(iter.Tok, "$_OldIterHeap", Predef.HeapType), iter);
      var old_nw = new OldExpr(iter.Tok, nw);
      old_nw.Type = nw.Type;  // resolve here
      var setDiff = new BinaryExpr(iter.Tok, BinaryExpr.Opcode.Sub, nw, old_nw);
      setDiff.ResolvedOp = BinaryExpr.ResolvedOpcode.SetDifference; setDiff.Type = nw.Type;  // resolve here
      Expression cond = new FreshExpr(iter.Tok, setDiff);
      cond.Type = Type.Bool;  // resolve here
      builder.Add(TrAssumeCmd(iter.Tok, yeEtran.TrExpr(cond)));

      // check wellformedness of postconditions
      var yeBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
      var endBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
      // In the yield-ensures case:  assume this.Valid();
      yeBuilder.Add(TrAssumeCmdWithDependencies(yeEtran, iter.Tok, validCall, "iterator validity"));
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var thisY = new MemberSelectExpr(iter.Tok, th, y);
        var thisYs = new MemberSelectExpr(iter.Tok, th, ys);
        var oldThisYs = new OldExpr(iter.Tok, thisYs);
        oldThisYs.Type = thisYs.Type;  // resolve here
        var singleton = new SeqDisplayExpr(iter.Tok, new List<Expression>() { thisY });
        singleton.Type = thisYs.Type;  // resolve here
        var concat = new BinaryExpr(iter.Tok, BinaryExpr.Opcode.Add, oldThisYs, singleton);
        concat.ResolvedOp = BinaryExpr.ResolvedOpcode.Concat; concat.Type = oldThisYs.Type;  // resolve here

        // In the yield-ensures case:  assume this.ys == old(this.ys) + [this.y];
        yeBuilder.Add(TrAssumeCmd(iter.Tok, Bpl.Expr.Eq(yeEtran.TrExpr(thisYs), yeEtran.TrExpr(concat))));
        // In the ensures case:  assume this.ys == old(this.ys);
        endBuilder.Add(TrAssumeCmd(iter.Tok, Bpl.Expr.Eq(yeEtran.TrExpr(thisYs), yeEtran.TrExpr(oldThisYs))));
      }

      foreach (var p in iter.YieldEnsures) {
        CheckWellformedAndAssume(p.E, wfOptions, localVariables, yeBuilder, yeEtran, "iterator yield-ensures clause");
      }
      foreach (var p in iter.Ensures) {
        CheckWellformedAndAssume(p.E, wfOptions, localVariables, endBuilder, yeEtran, "iterator ensures clause");
      }
      builder.Add(new Bpl.IfCmd(iter.Tok, null, yeBuilder.Collect(iter.Tok), null, endBuilder.Collect(iter.Tok)));

      Bpl.StmtList stmts = builder.Collect(iter.Tok);

      if (EmitImplementation(iter.Attributes)) {
        QKeyValue kv = etran.TrAttributes(iter.Attributes, null);
        AddImplementationWithAttributes(GetToken(iter), proc, inParams, new List<Variable>(),
          localVariables, stmts, kv);
      }

      Reset();
    }

    void AddIteratorImpl(IteratorDecl iter, Bpl.Procedure proc) {
      Contract.Requires(iter != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(iter.Body != null);
      Contract.Requires(currentModule == null && codeContext == null && yieldCountVariable == null && _tmpIEs.Count == 0);
      Contract.Ensures(currentModule == null && codeContext == null && yieldCountVariable == null && _tmpIEs.Count == 0);

      proofDependencies.SetCurrentDefinition(proc.VerboseName, iter);
      currentModule = iter.EnclosingModuleDefinition;
      codeContext = iter;

      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Contract.Assert(1 <= inParams.Count);  // there should at least be a receiver parameter
      Contract.Assert(proc.OutParams.Count == 0);

      var builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(iter.ContainsHide));
      var etran = new ExpressionTranslator(this, Predef, iter.Tok, iter);
      // Don't do reads checks since iterator reads clauses mean something else.
      // See comment inside GenerateIteratorImplPrelude().
      etran = etran.WithReadsFrame(null);
      var localVariables = new Variables();
      GenerateIteratorImplPrelude(iter, inParams, new List<Variable>(), builder, localVariables, etran);

      // add locals for the yield-history variables and the extra variables
      // Assume the precondition and postconditions of the iterator constructor method
      foreach (var p in iter.Member_Init.Req) {
        if (p.Label != null) {
          // don't include this precondition here
          Contract.Assert(p.Label.E != null);  // it should already have been recorded
        } else {
          builder.Add(TrAssumeCmdWithDependencies(etran, p.E.Tok, p.E, "iterator constructor requires clause"));
        }
      }
      foreach (var p in iter.Member_Init.Ens) {
        // these postconditions are two-state predicates, but that's okay, because we haven't changed anything yet
        builder.Add(TrAssumeCmdWithDependencies(etran, p.E.Tok, p.E, "iterator constructor ensures clause"));
      }
      // add the _yieldCount variable, and assume its initial value to be 0
      yieldCountVariable = (Bpl.LocalVariable)localVariables.GetOrAdd(new Bpl.LocalVariable(iter.Tok,
        new Bpl.TypedIdent(iter.Tok, iter.YieldCountVariable.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(iter.YieldCountVariable.Type))));
      yieldCountVariable.TypedIdent.WhereExpr = YieldCountAssumption(iter, etran);  // by doing this after setting "yieldCountVariable", the variable can be used by YieldCountAssumption
      builder.Add(TrAssumeCmd(iter.Tok, Bpl.Expr.Eq(new Bpl.IdentifierExpr(iter.Tok, yieldCountVariable), Bpl.Expr.Literal(0))));
      // add a variable $_OldIterHeap
      var oih = new Bpl.IdentifierExpr(iter.Tok, "$_OldIterHeap", Predef.HeapType);
      Bpl.Expr wh = BplAnd(
        FunctionCall(iter.Tok, BuiltinFunction.IsGoodHeap, null, oih),
        HeapSucc(oih, etran.HeapExpr));
      localVariables.GetOrAdd(new Bpl.LocalVariable(iter.Tok, new Bpl.TypedIdent(iter.Tok, "$_OldIterHeap", Predef.HeapType, wh)));

      // do an initial YieldHavoc
      YieldHavoc(iter.Tok, iter, builder, etran);

      // translate the body of the iterator
      var stmts = TrStmt2StmtList(builder, iter.Body, localVariables, etran);

      if (EmitImplementation(iter.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(iter.Attributes, null);

        AddImplementationWithAttributes(GetToken(iter), proc, inParams,
          new List<Variable>(), localVariables, stmts, kv);
      }

      yieldCountVariable = null;
      Reset();
    }

    Bpl.Expr YieldCountAssumption(IteratorDecl iter, ExpressionTranslator etran) {
      Contract.Requires(iter != null);
      Contract.Requires(etran != null);
      Contract.Requires(yieldCountVariable != null);
      Bpl.Expr wh = Bpl.Expr.True;
      foreach (var ys in iter.OutsHistoryFields) {
        // add the conjunct:  _yieldCount == |this.ys|
        wh = BplAnd(wh, Bpl.Expr.Eq(new Bpl.IdentifierExpr(iter.Tok, yieldCountVariable),
          FunctionCall(iter.Tok, BuiltinFunction.SeqLength, null,
            ApplyUnbox(iter.Tok, ReadHeap(iter.Tok, etran.HeapExpr,
              new Bpl.IdentifierExpr(iter.Tok, etran.This, Predef.RefType),
              new Bpl.IdentifierExpr(iter.Tok, GetField(ys))), TrType(ys.Type)))));
      }
      return wh;
    }

    void GenerateIteratorImplPrelude(IteratorDecl iter, List<Variable> inParams, List<Variable> outParams,
      BoogieStmtListBuilder builder, Variables localVariables, ExpressionTranslator etran) {
      Contract.Requires(iter != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(Predef != null);

      // set up the information used to verify the method's modifies clause
      var iteratorFrame = new List<FrameExpression>();
      var th = new ThisExpr(iter);
      iteratorFrame.Add(new FrameExpression(iter.Tok, th, null));
      iteratorFrame.AddRange(iter.Modifies.Expressions);
      // Note we explicitly do NOT use iter.Reads, because reads clauses on iterators
      // mean something different from reads clauses on functions or methods:
      // the memory locations that are not havoced by a yield statement.
      // Look for the references to the YieldHavoc, IterHavoc0 and IterHavoc1 DafnyPrelude.bpl functions for details.
      Contract.Assert(etran.readsFrame == null);
      DefineFrame(iter.Tok, etran.ModifiesFrame(iter.Tok), iteratorFrame, builder, localVariables, null);
      builder.AddCaptureState(iter.Tok, false, "initial state");
    }

    /// <summary>
    /// Generate:
    ///   havoc Heap \ {this} \ _reads \ _new;
    ///   assume this.Valid();
    ///   assume YieldRequires;
    ///   $_OldIterHeap := Heap;
    /// </summary>
    void YieldHavoc(IOrigin tok, IteratorDecl iter, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(iter != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      // havoc Heap \ {this} \ _reads \ _new;
      var th = new ThisExpr(iter);
      var rds = new MemberSelectExpr(tok, th, iter.Member_Reads);
      var nw = new MemberSelectExpr(tok, th, iter.Member_New);
      builder.Add(Call(builder.Context, tok, "$YieldHavoc",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(rds), etran.TrExpr(nw) },
        new List<Bpl.IdentifierExpr>()));
      // assume YieldRequires;
      foreach (var p in iter.YieldRequires) {
        builder.Add(TrAssumeCmdWithDependencies(etran, tok, p.E, "iterator yield-requires clause"));
      }
      // $_OldIterHeap := Heap;
      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, "$_OldIterHeap", Predef.HeapType), etran.HeapExpr));
    }
  }
}
