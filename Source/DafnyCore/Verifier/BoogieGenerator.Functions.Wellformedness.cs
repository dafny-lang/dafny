using System.Collections.Generic;
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
        MethodTranslationKind.SpecWellformedness), f);
      generator.currentModule = f.EnclosingClass.EnclosingModuleDefinition;
      generator.codeContext = f;

      ExpressionTranslator ordinaryEtran = new ExpressionTranslator(generator, generator.Predef, f.Tok, f);
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

      var context = new BodyTranslationContext(f.ContainsHide);
      var ens = new List<Bpl.Ensures>();
      foreach (AttributedExpression ensures in f.Ens) {
        var functionHeight = generator.currentModule.CallGraph.GetSCCRepresentativePredecessorCount(f);
        var splits = new List<SplitExprInfo>();
        bool splitHappened /*we actually don't care*/ = generator.TrSplitExpr(context, ensures.E, splits, true, functionHeight, true, etran);
        var (errorMessage, successMessage) = generator.CustomErrorMessage(ensures.Attributes);
        foreach (var s in splits) {
          if (s.IsChecked && !s.Tok.IsInherited(generator.currentModule)) {
            generator.AddEnsures(ens, generator.EnsuresWithDependencies(s.Tok, false, ensures.E, s.E, errorMessage, successMessage, null));
          }
        }
      }

      var selfCall = GetSelfCall(f, etran, procedureParameters);
      // Enforce 'older' conditions
      var (olderParameterCount, olderCondition) = generator.OlderCondition(f, selfCall, procedureParameters);
      if (olderParameterCount != 0) {
        generator.AddEnsures(ens, new Ensures(f.Tok, false, olderCondition, null) {
          Description = new IsOlderProofObligation(olderParameterCount, f.Ins.Count + (f.IsStatic ? 0 : 1))
        });
      }

      var proc = new Procedure(f.Tok, "CheckWellformed" + NameSeparator + f.FullSanitizedName,
        new List<TypeVariable>(),
        Concat(Concat(typeInParams, heapParameters), procedureParameters), outParams,
        false, requires, mod, ens, etran.TrAttributes(f.Attributes, null));
      AddVerboseNameAttribute(proc, f.FullDafnyName, MethodTranslationKind.SpecWellformedness);
      generator.sink.AddTopLevelDeclaration(proc);

      if (generator.InsertChecksums) {
        generator.InsertChecksum(f, proc, true);
      }

      Contract.Assert(proc.InParams.Count == typeInParams.Count + heapParameters.Count + procedureParameters.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var locals = new Variables();
      var builder = new BoogieStmtListBuilder(generator, generator.options, context);
      var builderInitializationArea = new BoogieStmtListBuilder(generator, generator.options, context);
      if (f is TwoStateFunction) {
        // $Heap := current$Heap;
        var heap = ordinaryEtran.HeapCastToIdentifierExpr;
        builder.Add(Cmd.SimpleAssign(f.Tok, heap, etran.HeapExpr));
        etran = ordinaryEtran; // we no longer need the special heap names
      }

      builder.AddCaptureState(f.Tok, false, "initial state");

      generator.DefineFrame(f.Tok, etran.ReadsFrame(f.Tok), f.Reads.Expressions, builder, locals, null);
      generator.InitializeFuelConstant(f.Tok, builder, etran);

      var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, builder);

      // Check well-formedness of any default-value expressions (before assuming preconditions).
      delayer.DoWithDelayedReadsChecks(true, wfo => {
        foreach (var formal in f.Ins.Where(formal => formal.DefaultValue != null)) {
          var e = formal.DefaultValue;
          generator.CheckWellformed(e, wfo, locals, builder,
            etran.WithReadsFrame(etran.readsFrame, null)); // No frame scope for default values
          builder.Add(new AssumeCmd(e.Tok, etran.CanCallAssumption(e)));
          generator.CheckSubrange(e.Tok, etran.TrExpr(e), e.Type, formal.Type, e, builder);

          if (formal.IsOld) {
            Expr wh = generator.GetWhereClause(e.Tok, etran.TrExpr(e), e.Type, etran.Old, ISALLOC, true);
            if (wh != null) {
              var desc = new IsAllocated("default value", "in the two-state function's previous state", e);
              builder.Add(generator.Assert(generator.GetToken(e), wh, desc, builder.Context));
            }
          }
        }
      });

      // Check well-formedness of the preconditions (including termination), and then
      // assume each one of them.  After all that (in particular, after assuming all
      // of them), do the postponed reads checks.
      delayer.DoWithDelayedReadsChecks(false, wfo => {
        builder.Add(new CommentCmd("Check well-formedness of preconditions, and then assume them"));
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
      builder.Add(new CommentCmd("Check well-formedness of the reads clause"));
      delayer.DoWithDelayedReadsChecks(false,
        wfo => { generator.CheckFrameWellFormed(wfo, f.Reads.Expressions, locals, builder, etran); });

      ConcurrentAttributeCheck(f, etran, builder);

      // check well-formedness of the decreases clauses (including termination, but no reads checks)
      builder.Add(new CommentCmd("Check well-formedness of the decreases clause"));
      foreach (Expression p in f.Decreases.Expressions) {
        generator.CheckWellformed(p, new WFOptions(null, false), locals, builder, etran);
      }

      var implementationParameters = Bpl.Formal.StripWhereClauses(procedureParameters);
      CheckBodyAndEnsuresClauseWellformedness(f, etran, locals, implementationParameters, builderInitializationArea, builder);

      if (generator.EmitImplementation(f.Attributes)) {
        var s0 = builderInitializationArea.Collect(f.Tok);
        var s1 = builder.Collect(f.Tok);
        var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), f.Tok);

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

    private void ConcurrentAttributeCheck(Function f, ExpressionTranslator etran, BoogieStmtListBuilder builder) {
      // If the function is marked as {:concurrent}, check that the reads clause is empty.
      if (Attributes.Contains(f.Attributes, Attributes.ConcurrentAttributeName)) {
        var desc = new ConcurrentFrameEmpty(f, "reads");
        generator.CheckFrameEmpty(f.Tok, etran, etran.ReadsFrame(f.Tok), builder, desc, null);
      }
    }

    private void CheckBodyAndEnsuresClauseWellformedness(Function f, ExpressionTranslator etran, Variables locals, List<Variable> inParams,
      BoogieStmtListBuilder builderInitializationArea, BoogieStmtListBuilder builder) {
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
      builder.Add(new IfCmd(f.Tok, null, postCheckBuilder.Collect(f.Tok), null, bodyCheckBuilder.Collect(f.Tok)));
    }

    private BoogieStmtListBuilder GetBodyCheckBuilder(Function f, ExpressionTranslator etran,
      List<Variable> parameters,
      Variables locals, BoogieStmtListBuilder builderInitializationArea) {
      var selfCall = GetSelfCall(f, etran, parameters);
      var context = new BodyTranslationContext(f.ContainsHide);
      var bodyCheckBuilder = new BoogieStmtListBuilder(generator, generator.options, context);
      bodyCheckBuilder.Add(new CommentCmd("Check well-formedness of body and result subset type constraint"));
      if (f.Body != null && generator.RevealedInScope(f)) {
        var doReadsChecks = etran.readsFrame != null;
        var wfo = new WFOptions(null, doReadsChecks, doReadsChecks, false);

        void CheckPostcondition(BoogieStmtListBuilder innerBuilder, Expression innerBody) {
          generator.CheckSubsetType(etran, innerBody, selfCall, f.ResultType, innerBuilder, "function call result");
          if (f.Result != null) {
            var cmd = TrAssumeCmd(f.Tok, Expr.Eq(selfCall, generator.TrVar(f.Tok, f.Result)));
            generator.proofDependencies?.AddProofDependencyId(cmd, f.Tok, new FunctionDefinitionDependency(f));
            innerBuilder.Add(cmd);
          }
          if (doReadsChecks) {
            // assert b$reads_guards#0;  ...
            foreach (var a in wfo.CreateAsserts) {
              innerBuilder.Add(a());
            }
          }

          innerBuilder.Add(new ReturnCmd(innerBody.Tok));
        }

        generator.CheckWellformedWithResult(f.Body, wfo, locals, bodyCheckBuilder, etran, CheckPostcondition);

        // var b$reads_guards#0 : bool  ...
        locals.AddRange(wfo.Locals.Values);
        // b$reads_guards#0 := true   ...
        foreach (var cmd in wfo.AssignLocals) {
          builderInitializationArea.Add(cmd);
        }
      }
      bodyCheckBuilder.Add(TrAssumeCmd(f.Tok, Expr.False));

      return bodyCheckBuilder;
    }

    private Expr GetSelfCall(Function f, ExpressionTranslator etran, List<Variable> parameters) {
      var funcId = new FunctionCall(new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName, generator.TrType(f.ResultType)));
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
        args.Add(new Bpl.IdentifierExpr(f.Tok, parameter));
      }

      Expr funcAppl = new NAryExpr(f.Tok, funcId, args);
      return funcAppl;
    }

    private BoogieStmtListBuilder GetPostCheckBuilder(Function f, ExpressionTranslator etran, Variables locals) {
      var context = new BodyTranslationContext(f.ContainsHide);
      var postCheckBuilder = new BoogieStmtListBuilder(generator, generator.options, context);
      postCheckBuilder.Add(new CommentCmd("Check well-formedness of postcondition and assume false"));

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
        args.Add(new Bpl.IdentifierExpr(f.Tok, etran.This));
      }

      foreach (var p in f.Ins) {
        args.Add(new Bpl.IdentifierExpr(p.Tok, p.AssignUniqueName(f.IdGenerator), generator.TrType(p.Type)));
      }

      Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName, generator.TrType(f.ResultType));
      Expr funcAppl = new NAryExpr(f.Tok, new FunctionCall(funcID), args);

      var wh = generator.GetWhereClause(f.Tok, funcAppl, f.ResultType, etran, NOALLOC);
      if (wh != null) {
        postCheckBuilder.Add(TrAssumeCmd(f.Tok, wh));
        if (f.Result != null) {
          var resultVarId = new Bpl.IdentifierExpr(f.Result.Tok, f.Result.AssignUniqueName(f.IdGenerator), generator.TrType(f.Result.Type));
          wh = generator.GetWhereClause(f.Result.Tok, resultVarId, f.Result.Type, etran, NOALLOC);
          postCheckBuilder.Add(TrAssumeCmd(f.Result.Tok, wh));
        }
      }
      // Now for the ensures clauses
      foreach (AttributedExpression p in f.Ens) {
        // assume the postcondition for the benefit of checking the remaining postconditions
        generator.CheckWellformedAndAssume(p.E, new WFOptions(f, false), locals, postCheckBuilder, etran, "ensures clause");
      }

      postCheckBuilder.Add(TrAssumeCmd(f.Tok, Expr.False));
      return postCheckBuilder;
    }

    private ExpressionTranslator GetExpressionTranslator(Function f, ExpressionTranslator ordinaryEtran,
      out List<Bpl.Requires> additionalRequires, out List<Variable> inParams_Heap) {
      ExpressionTranslator etran;
      additionalRequires = new();
      inParams_Heap = new List<Variable>();
      if (f is TwoStateFunction) {
        var prevHeapVar = new Bpl.Formal(f.Tok, new TypedIdent(f.Tok, "previous$Heap", generator.Predef.HeapType), true);
        var currHeapVar = new Bpl.Formal(f.Tok, new TypedIdent(f.Tok, "current$Heap", generator.Predef.HeapType), true);
        inParams_Heap.Add(prevHeapVar);
        inParams_Heap.Add(currHeapVar);
        Expr prevHeap = new Bpl.IdentifierExpr(f.Tok, prevHeapVar);
        Expr currHeap = new Bpl.IdentifierExpr(f.Tok, currHeapVar);
        etran = new ExpressionTranslator(generator, generator.Predef, currHeap, prevHeap, f);

        // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
        var a0 = Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
        var a1 = generator.HeapSucc(prevHeap, currHeap);
        var a2 = generator.FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, currHeap);
        additionalRequires.Add(generator.Requires(f.Tok, true, null, BplAnd(a0, BplAnd(a1, a2)), null, null, null));
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
        // Note, this variable should NOT have a "where" clause, because it gets assumed already at the beginning of the CheckWellformed procedure
        outParams.Add(new Bpl.Formal(p.Tok, new TypedIdent(p.Tok, p.AssignUniqueName(f.IdGenerator), varType), true));
      }

      return outParams;
    }

    private List<Bpl.Requires> GetWellformednessProcedureRequires(Function f, ExpressionTranslator etran) {
      var requires = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      requires.Add(generator.Requires(f.Tok, true, null, etran.HeightContext(f), null, null, null));

      foreach (var typeBoundAxiom in generator.TypeBoundAxioms(f.Tok, Concat(f.EnclosingClass.TypeArgs, f.TypeArgs))) {
        requires.Add(generator.Requires(f.Tok, true, null, typeBoundAxiom, null, null, null));
      }

      return requires;
    }

    private List<Variable> GetParameters(Function f, ExpressionTranslator etran) {
      var inParams = new List<Variable>();
      if (!f.IsStatic) {
        var th = new Bpl.IdentifierExpr(f.Tok, "this", generator.TrReceiverType(f));
        Expr wh = BplAnd(
          generator.ReceiverNotNull(th),
          (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.Tok, th, ModuleResolver.GetReceiverType(f.Tok, f)));
        Bpl.Formal thVar = new Bpl.Formal(f.Tok, new TypedIdent(f.Tok, "this", generator.TrReceiverType(f), wh), true);
        inParams.Add(thVar);
      }

      foreach (Formal parameter in f.Ins) {
        Bpl.Type varType = generator.TrType(parameter.Type);
        Expr wh = generator.GetWhereClause(parameter.Tok,
          new Bpl.IdentifierExpr(parameter.Tok, parameter.AssignUniqueName(f.IdGenerator), varType), parameter.Type,
          parameter.IsOld ? etran.Old : etran, f is TwoStateFunction ? ISALLOC : NOALLOC);
        inParams.Add(new Bpl.Formal(parameter.Tok,
          new TypedIdent(parameter.Tok, parameter.AssignUniqueName(f.IdGenerator), varType, wh), true));
      }

      return inParams;
    }
  }
}