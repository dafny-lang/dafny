using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  class FunctionWellformednessChecker {
    private readonly BoogieGenerator generator;

    public FunctionWellformednessChecker(BoogieGenerator generator) {
      this.generator = generator;
    }

    public void Check(Function f) {

      Contract.Assert(generator.InVerificationScope(f));

      generator.proofDependencies.SetCurrentDefinition(MethodVerboseName(f.FullDafnyName,
        MethodTranslationKind.SpecWellformedness));
      generator.currentModule = f.EnclosingClass.EnclosingModuleDefinition;
      generator.codeContext = f;

      ExpressionTranslator ordinaryEtran = new ExpressionTranslator(generator, generator.predef, f.tok, f);
      var etran = GetExpressionTranslator(f, ordinaryEtran, out var additionalRequires, out var heapParameters);

      // parameters of the procedure
      var typeInParams = generator.MkTyParamFormals(GetTypeParams(f), true);
      var procedureParameters = GetParameters(f, etran);
      var outParams = GetWellformednessProcedureOutParameters(f, etran);
      var requires = GetWellformednessProcedureRequires(f, etran);
      requires.AddRange(additionalRequires);
      
      // modifies $Heap
      var mod = new List<Bpl.IdentifierExpr> {
        ordinaryEtran.HeapCastToIdentifierExpr,
      };

      var proc = new Procedure(f.tok, "CheckWellformed" + NameSeparator + f.FullSanitizedName,
        new List<TypeVariable>(),
        Concat(Concat(typeInParams, heapParameters), procedureParameters), outParams,
        false, requires, mod, new List<Ensures>(), etran.TrAttributes(f.Attributes, null));
      AddVerboseNameAttribute(proc, f.FullDafnyName, MethodTranslationKind.SpecWellformedness);
      generator.sink.AddTopLevelDeclaration(proc);

      if (generator.InsertChecksums) {
        generator.InsertChecksum(f, proc, true);
      }

      Contract.Assert(proc.InParams.Count == typeInParams.Count + heapParameters.Count + procedureParameters.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(generator, generator.options);
      var builderInitializationArea = new BoogieStmtListBuilder(generator, generator.options);
      if (f is TwoStateFunction) {
        // $Heap := current$Heap;
        var heap = ordinaryEtran.HeapCastToIdentifierExpr;
        builder.Add(Cmd.SimpleAssign(f.tok, heap, etran.HeapExpr));
        etran = ordinaryEtran; // we no longer need the special heap names
      }

      builder.AddCaptureState(f.tok, false, "initial state");

      generator.DefineFrame(f.tok, etran.ReadsFrame(f.tok), f.Reads.Expressions, builder, locals, null);
      generator.InitializeFuelConstant(f.tok, builder, etran);

      var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, builder);

      // Check well-formedness of any default-value expressions (before assuming preconditions).
      delayer.DoWithDelayedReadsChecks(true, wfo => {
        foreach (var formal in f.Ins.Where(formal => formal.DefaultValue != null)) {
          var e = formal.DefaultValue;
          generator.CheckWellformed(e, wfo, locals, builder,
            etran.WithReadsFrame(etran.readsFrame, null)); // No frame scope for default values
          builder.Add(new AssumeCmd(e.tok, etran.CanCallAssumption(e)));
          generator.CheckSubrange(e.tok, etran.TrExpr(e), e.Type, formal.Type, e, builder);

          if (formal.IsOld) {
            Expr wh = generator.GetWhereClause(e.tok, etran.TrExpr(e), e.Type, etran.Old, ISALLOC, true);
            if (wh != null) {
              var desc = new PODesc.IsAllocated("default value", "in the two-state function's previous state", e);
              builder.Add(generator.Assert(generator.GetToken(e), wh, desc));
            }
          }
        }
      });

      // Check well-formedness of the preconditions (including termination), and then
      // assume each one of them.  After all that (in particular, after assuming all
      // of them), do the postponed reads checks.
      delayer.DoWithDelayedReadsChecks(false, wfo => {
        builder.Add(new CommentCmd("Check Wfness of preconditions, and then assume them"));
        foreach (AttributedExpression require in f.Req) {
          if (require.Label != null) {
            require.Label.E = (f is TwoStateFunction ? ordinaryEtran : etran.Old).TrExpr(require.E);
            generator.CheckWellformed(require.E, wfo, locals, builder, etran);
          } else {
            generator.CheckWellformedAndAssume(require.E, wfo, locals, builder, etran, "requires clause");
          }
        }
      });

      // Check well-formedness of the reads clause.  Note that this is done after assuming
      // the preconditions.  In other words, the well-formedness of the reads clause is
      // allowed to assume the precondition (yet, the requires clause is checked to
      // read only those things indicated in the reads clause).
      builder.Add(new CommentCmd("Check Wfness of the reads clause"));
      delayer.DoWithDelayedReadsChecks(false,
        wfo => { generator.CheckFrameWellFormed(wfo, f.Reads.Expressions, locals, builder, etran); });

      ConcurrentAttributeCheck(f, etran, builder);

      // check well-formedness of the decreases clauses (including termination, but no reads checks)
      builder.Add(new CommentCmd("Check Wfness of the decreases clause"));
      foreach (Expression p in f.Decreases.Expressions) {
        generator.CheckWellformed(p, new WFOptions(null, false), locals, builder, etran);
      }
      
      var implementationParameters = Bpl.Formal.StripWhereClauses(procedureParameters);
      CheckBodyAndEnsuresClauses(f, etran, locals, implementationParameters, builderInitializationArea, builder);
      
      if (generator.EmitImplementation(f.Attributes)) {
        var s0 = builderInitializationArea.Collect(f.tok);
        var s1 = builder.Collect(f.tok);
        var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), f.tok);
        
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(f.Attributes, null);
        var parameters = Concat(Concat(Bpl.Formal.StripWhereClauses(typeInParams), heapParameters), implementationParameters);
        var impl = generator.AddImplementationWithAttributes(generator.GetToken(f), proc,
          parameters,
          Bpl.Formal.StripWhereClauses(outParams),
          locals, implBody, kv);
        if (generator.InsertChecksums) {
          generator.InsertChecksum(f, impl);
        }
      }

      Contract.Assert(generator.currentModule == f.EnclosingClass.EnclosingModuleDefinition);
      Contract.Assert(generator.codeContext == f);
      generator.Reset();
    }

    // TODO should be moved so its injected
    private void ConcurrentAttributeCheck(Function f, ExpressionTranslator etran, BoogieStmtListBuilder builder)
    {
      // If the function is marked as {:concurrent}, check that the reads clause is empty.
      if (Attributes.Contains(f.Attributes, Attributes.ConcurrentAttributeName)) {
        var desc = new PODesc.ConcurrentFrameEmpty(f, "reads");
        generator.CheckFrameEmpty(f.tok, etran, etran.ReadsFrame(f.tok), builder, desc, null);
      }
    }

    private void CheckBodyAndEnsuresClauses(Function f, ExpressionTranslator etran, List<Variable> locals, List<Variable> inParams,
      BoogieStmtListBuilder builderInitializationArea, BoogieStmtListBuilder builder)
    {
      builder.Add(new CommentCmd("Check body and ensures clauses"));
      // Generate:
      //   if (*) {
      //     check well-formedness of postcondition
      //     assume false;  // don't go on to check the postconditions
      //   } else {
      //     check well-formedness of body
      //     // fall through to check the postconditions themselves
      //   }
      // Here go the postconditions (termination checks included, but no reads checks)
      var postCheckBuilder = GetPostCheckBuilder(f, etran, locals);

      // Here goes the body (and include both termination checks and reads checks)
      var bodyCheckBuilder = GetBodyCheckBuilder(f, etran, inParams, locals, builderInitializationArea);

      // Combine the two, letting the postcondition be checked on after the "bodyCheckBuilder" branch
      builder.Add(new IfCmd(f.tok, null, postCheckBuilder.Collect(f.tok), null, bodyCheckBuilder.Collect(f.tok)));
    }

    private BoogieStmtListBuilder GetBodyCheckBuilder(Function f, ExpressionTranslator etran,
      List<Variable> parameters,
      List<Variable> locals, BoogieStmtListBuilder builderInitializationArea)
    {
      var selfCall = GetSelfCall(f, etran, parameters);
      var bodyCheckBuilder = new BoogieStmtListBuilder(generator, generator.options);
      bodyCheckBuilder.Add(new CommentCmd("Check Wfness of body, result subset type constraint, and return to check the postcondition"));
      if (f.Body != null && generator.RevealedInScope(f)) {
        var bodyCheckDelayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, bodyCheckBuilder);
        bodyCheckDelayer.DoWithDelayedReadsChecks(false, wfo => {
          Action<BoogieStmtListBuilder> checkPostcondition = b => {
            Contract.Assert(f.ResultType != null);
            var bResult = etran.TrExpr(f.Body);
            generator.CheckSubrange(f.Body.tok, bResult, f.Body.Type, f.ResultType, f.Body, b);
          };
          generator.CheckWellformedWithResult(f.Body, wfo, checkPostcondition, locals, bodyCheckBuilder, etran);
          bodyCheckBuilder.Add(generator.TrAssumeCmdWithDependenciesAndExtend(etran, f.Body.tok, f.Body,
            e => Bpl.Expr.Eq(selfCall, generator.AdaptBoxing(f.Body.tok, e, f.Body.Type, f.ResultType)),
            "function call result"));
          bodyCheckBuilder.Add(TrAssumeCmd(f.Body.tok, etran.CanCallAssumption(f.Body)));
          bodyCheckBuilder.Add(new CommentCmd("CheckWellformedWithResult: any expression"));
          bodyCheckBuilder.Add(TrAssumeCmd(f.Body.tok, generator.MkIs(selfCall, f.ResultType)));
          if (f.Result != null) {
            var cmd = TrAssumeCmd(f.tok, Expr.Eq(selfCall, generator.TrVar(f.tok, f.Result)));
            generator.proofDependencies?.AddProofDependencyId(cmd, f.tok, new FunctionDefinitionDependency(f));
            bodyCheckBuilder.Add(cmd);
          }

          foreach (AttributedExpression e in f.Ens) {
            var functionHeight = generator.currentModule.CallGraph.GetSCCRepresentativePredecessorCount(f);
            var splits = new List<SplitExprInfo>();
            bool splitHappened /*we actually don't care*/ =
              generator.TrSplitExpr(e.E, splits, true, functionHeight, true, true, etran);
            var (errorMessage, successMessage) = generator.CustomErrorMessage(e.Attributes);
            foreach (var s in splits) {
              if (s.IsChecked && !RefinementToken.IsInherited(s.Tok, generator.currentModule)) {
                var ensures =
                  generator.EnsuresWithDependencies(s.Tok, false, e.E, s.E, errorMessage, successMessage, null);
                bodyCheckBuilder.Add(new AssertCmd(ensures.tok, ensures.Condition, ensures.Description,
                  ensures.Attributes));
              }
            }
          }
        });

        // Enforce 'older' conditions
        var (olderParameterCount, olderCondition) = generator.OlderCondition(f, selfCall, parameters);
        if (olderParameterCount != 0) {
          bodyCheckBuilder.Add(generator.Assert(f.tok, olderCondition,
            new PODesc.IsOlderProofObligation(olderParameterCount, f.Ins.Count + (f.IsStatic ? 0 : 1))));
        }
      }

      return bodyCheckBuilder;
    }

    private Expr GetSelfCall(Function f, ExpressionTranslator etran, List<Variable> parameters)
    {
      var funcId = new FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, generator.TrType(f.ResultType)));
      var args = new List<Expr>();
      foreach (var p in GetTypeParams(f)) {
        args.Add(generator.TrTypeParameter(p));
      }

      if (f.IsFuelAware()) {
        args.Add(etran.layerInterCluster.GetFunctionFuel(f));
      }

      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(generator.options)) {
        args.Add(generator.GetRevealConstant(f));
      }

      if (f is TwoStateFunction) {
        args.Add(etran.Old.HeapExpr);
      }

      if (f.ReadsHeap) {
        args.Add(etran.HeapExpr);
      }

      foreach (Variable parameter in parameters) {
        args.Add(new Bpl.IdentifierExpr(f.tok, parameter));
      }

      Expr funcAppl = new NAryExpr(f.tok, funcId, args);
      return funcAppl;
    }

    private BoogieStmtListBuilder GetPostCheckBuilder(Function f, ExpressionTranslator etran, List<Variable> locals)
    {
      var postCheckBuilder = new BoogieStmtListBuilder(generator, generator.options);
      postCheckBuilder.Add(new CommentCmd("Check Wfness of postcondition and assume false"));
      
      // Assume the type returned by the call itself respects its type (this matters if the type is "nat", for example)
      var args = new List<Expr>();
      foreach (var p in GetTypeParams(f)) {
        args.Add(generator.TrTypeParameter(p));
      }

      if (f.IsFuelAware()) {
        args.Add(etran.layerInterCluster.GetFunctionFuel(f));
      }

      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(generator.options)) {
        args.Add(generator.GetRevealConstant(f));
      }

      if (f is TwoStateFunction) {
        args.Add(etran.Old.HeapExpr);
      }

      if (f.ReadsHeap) {
        args.Add(etran.HeapExpr);
      }

      if (!f.IsStatic) {
        args.Add(new Bpl.IdentifierExpr(f.tok, etran.This));
      }

      foreach (var p in f.Ins) {
        args.Add(new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), generator.TrType(p.Type)));
      }

      Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, generator.TrType(f.ResultType));
      Expr funcAppl = new NAryExpr(f.tok, new FunctionCall(funcID), args);

      var wh = generator.GetWhereClause(f.tok, funcAppl, f.ResultType, etran, NOALLOC);
      if (wh != null) {
          postCheckBuilder.Add(TrAssumeCmd(f.tok, wh));
      }
      // Now for the ensures clauses
      foreach (AttributedExpression p in f.Ens) {
        // assume the postcondition for the benefit of checking the remaining postconditions
        generator.CheckWellformedAndAssume(p.E, new WFOptions(f, false), locals, postCheckBuilder, etran, "ensures clause");
      }

      postCheckBuilder.Add(TrAssumeCmd(f.tok, Expr.False));
      return postCheckBuilder;
    }

    private ExpressionTranslator GetExpressionTranslator(Function f, ExpressionTranslator ordinaryEtran,
      out List<Bpl.Requires> additionalRequires, out List<Variable> inParams_Heap)
    {
      ExpressionTranslator etran;
      additionalRequires = new();
      inParams_Heap = new List<Variable>();
      if (f is TwoStateFunction) {
        var prevHeapVar = new Bpl.Formal(f.tok, new TypedIdent(f.tok, "previous$Heap", generator.predef.HeapType), true);
        var currHeapVar = new Bpl.Formal(f.tok, new TypedIdent(f.tok, "current$Heap", generator.predef.HeapType), true);
        inParams_Heap.Add(prevHeapVar);
        inParams_Heap.Add(currHeapVar);
        Expr prevHeap = new Bpl.IdentifierExpr(f.tok, prevHeapVar);
        Expr currHeap = new Bpl.IdentifierExpr(f.tok, currHeapVar);
        etran = new ExpressionTranslator(generator, generator.predef, currHeap, prevHeap, f);
        
        // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
        var a0 = Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
        var a1 = generator.HeapSucc(prevHeap, currHeap);
        var a2 = generator.FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, currHeap);
        additionalRequires.Add(generator.Requires(f.tok, true, null, BplAnd(a0, BplAnd(a1, a2)), null, null, null));
      } else {
        etran = ordinaryEtran;
      }

      return etran;
    }

    private List<Variable> GetWellformednessProcedureOutParameters(Function f, ExpressionTranslator etran) {
      var outParams = new List<Variable>();
      if (f.Result != null) {
        Formal p = f.Result;
        Contract.Assert(!p.IsOld);
        Bpl.Type varType = generator.TrType(p.Type);
        Expr wh = generator.GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), varType),
          p.Type, etran, NOALLOC);
        outParams.Add(new Bpl.Formal(p.tok, new TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), varType, wh),
          true));
      }

      return outParams;
    }

    private List<Bpl.Requires> GetWellformednessProcedureRequires(Function f, ExpressionTranslator etran) {
      var requires = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      requires.Add(generator.Requires(f.tok, true, null, etran.HeightContext(f), null, null, null));

      foreach (var typeBoundAxiom in generator.TypeBoundAxioms(f.tok, Concat(f.EnclosingClass.TypeArgs, f.TypeArgs))) {
        requires.Add(generator.Requires(f.tok, true, null, typeBoundAxiom, null, null, null));
      }

      return requires;
    }

    private List<Variable> GetParameters(Function f, ExpressionTranslator etran) {
      var inParams = new List<Variable>();
      if (!f.IsStatic) {
        var th = new Bpl.IdentifierExpr(f.tok, "this", generator.TrReceiverType(f));
        Expr wh = BplAnd(
          generator.ReceiverNotNull(th),
          (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, th, ModuleResolver.GetReceiverType(f.tok, f)));
        Bpl.Formal thVar = new Bpl.Formal(f.tok, new TypedIdent(f.tok, "this", generator.TrReceiverType(f), wh), true);
        inParams.Add(thVar);
      }

      foreach (Formal parameter in f.Ins) {
        Bpl.Type varType = generator.TrType(parameter.Type);
        Expr wh = generator.GetWhereClause(parameter.tok,
          new Bpl.IdentifierExpr(parameter.tok, parameter.AssignUniqueName(f.IdGenerator), varType), parameter.Type,
          parameter.IsOld ? etran.Old : etran, f is TwoStateFunction ? ISALLOC : NOALLOC);
        inParams.Add(new Bpl.Formal(parameter.tok,
          new TypedIdent(parameter.tok, parameter.AssignUniqueName(f.IdGenerator), varType, wh), true));
      }

      return inParams;
    }
  }
}