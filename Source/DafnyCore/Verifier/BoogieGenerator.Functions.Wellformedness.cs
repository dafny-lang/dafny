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
        MethodTranslationKind.SpecWellformedness));
      generator.currentModule = f.EnclosingClass.EnclosingModuleDefinition;
      generator.codeContext = f;

      Expr prevHeap = null;
      Expr currHeap = null;
      var ordinaryEtran = new ExpressionTranslator(generator, generator.predef, f.tok, f);
      ExpressionTranslator etran;
      var inParams_Heap = new List<Variable>();
      if (f is TwoStateFunction) {
        var prevHeapVar = new Bpl.Formal(f.tok, new TypedIdent(f.tok, "previous$Heap", generator.predef.HeapType), true);
        var currHeapVar = new Bpl.Formal(f.tok, new TypedIdent(f.tok, "current$Heap", generator.predef.HeapType), true);
        inParams_Heap.Add(prevHeapVar);
        inParams_Heap.Add(currHeapVar);
        prevHeap = new Bpl.IdentifierExpr(f.tok, prevHeapVar);
        currHeap = new Bpl.IdentifierExpr(f.tok, currHeapVar);
        etran = new ExpressionTranslator(generator, generator.predef, currHeap, prevHeap, f);
      } else {
        etran = ordinaryEtran;
      }

      // parameters of the procedure
      var typeInParams = generator.MkTyParamFormals(GetTypeParams(f), true);
      var inParams = GetParameters(f, etran);
      var outParams = GetWellformednessProcedureOutParameters(f, etran);
      var requires = GetWellformednessProcedureRequires(f, etran, prevHeap, ordinaryEtran, currHeap);

      // modifies $Heap
      var mod = new List<Bpl.IdentifierExpr> {
        ordinaryEtran.HeapCastToIdentifierExpr,
      };
      var ensures = GetWellformnessProcedureEnsures(f, etran);

      var proc = new Procedure(f.tok, "CheckWellformed" + NameSeparator + f.FullSanitizedName,
        new List<TypeVariable>(),
        Concat(Concat(typeInParams, inParams_Heap), inParams), outParams,
        false, requires, mod, ensures, etran.TrAttributes(f.Attributes, null));
      AddVerboseNameAttribute(proc, f.FullDafnyName, MethodTranslationKind.SpecWellformedness);
      generator.sink.AddTopLevelDeclaration(proc);

      if (generator.InsertChecksums) {
        generator.InsertChecksum(f, proc, true);
      }

      Contract.Assert(proc.InParams.Count == typeInParams.Count + inParams_Heap.Count + inParams.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var implOutParams = Bpl.Formal.StripWhereClauses(outParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(generator, generator.options);
      var builderInitializationArea = new BoogieStmtListBuilder(generator, generator.options);
      builder.Add(new CommentCmd("AddWellformednessCheck for function " + f));
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
        foreach (AttributedExpression p in f.Req) {
          if (p.Label != null) {
            p.Label.E = (f is TwoStateFunction ? ordinaryEtran : etran.Old).TrExpr(p.E);
            generator.CheckWellformed(p.E, wfo, locals, builder, etran);
          } else {
            generator.CheckWellformedAndAssume(p.E, wfo, locals, builder, etran, "requires clause");
          }
        }
      });

      // Check well-formedness of the reads clause.  Note that this is done after assuming
      // the preconditions.  In other words, the well-formedness of the reads clause is
      // allowed to assume the precondition (yet, the requires clause is checked to
      // read only those things indicated in the reads clause).
      delayer.DoWithDelayedReadsChecks(false,
        wfo => { generator.CheckFrameWellFormed(wfo, f.Reads.Expressions, locals, builder, etran); });

      // If the function is marked as {:concurrent}, check that the reads clause is empty.
      if (Attributes.Contains(f.Attributes, Attributes.ConcurrentAttributeName)) {
        var desc = new PODesc.ConcurrentFrameEmpty(f, "reads");
        generator.CheckFrameEmpty(f.tok, etran, etran.ReadsFrame(f.tok), builder, desc, null);
      }

      // check well-formedness of the decreases clauses (including termination, but no reads checks)
      foreach (Expression p in f.Decreases.Expressions) {
        generator.CheckWellformed(p, new WFOptions(null, false), locals, builder, etran);
      }

      // Generate:
      //   if (*) {
      //     check well-formedness of postcondition
      //     assume false;  // don't go on to check the postconditions
      //   } else {
      //     check well-formedness of body
      //     // fall through to check the postconditions themselves
      //   }
      // Here go the postconditions (termination checks included, but no reads checks)
      BoogieStmtListBuilder postCheckBuilder = new BoogieStmtListBuilder(generator, generator.options);
      // Assume the type returned by the call itself respects its type (this matters if the type is "nat", for example)
      {
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
      }
      // Now for the ensures clauses
      foreach (AttributedExpression p in f.Ens) {
        // assume the postcondition for the benefit of checking the remaining postconditions
        generator.CheckWellformedAndAssume(p.E, new WFOptions(f, false), locals, postCheckBuilder, etran, "ensures clause");
      }

      // Here goes the body (and include both termination checks and reads checks)
      BoogieStmtListBuilder bodyCheckBuilder = new BoogieStmtListBuilder(generator, generator.options);
      if (f.Body == null || !generator.RevealedInScope(f)) {
        // don't fall through to postcondition checks
        bodyCheckBuilder.Add(TrAssumeCmd(f.tok, Expr.False));
      } else {
        var funcID = new FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, generator.TrType(f.ResultType)));
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

        foreach (Variable p in implInParams) {
          args.Add(new Bpl.IdentifierExpr(f.tok, p));
        }

        Expr funcAppl = new NAryExpr(f.tok, funcID, args);

        var bodyCheckDelayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, bodyCheckBuilder);
        bodyCheckDelayer.DoWithDelayedReadsChecks(false, wfo => {
          generator.CheckWellformedWithResult(f.Body, wfo, funcAppl, f.ResultType, locals, bodyCheckBuilder, etran,
            "function call result");
          if (f.Result != null) {
            var cmd = TrAssumeCmd(f.tok, Expr.Eq(funcAppl, generator.TrVar(f.tok, f.Result)));
            generator.proofDependencies?.AddProofDependencyId(cmd, f.tok, new FunctionDefinitionDependency(f));
            bodyCheckBuilder.Add(cmd);
          }
        });

        // Enforce 'older' conditions
        var (olderParameterCount, olderCondition) = generator.OlderCondition(f, funcAppl, implInParams);
        if (olderParameterCount != 0) {
          bodyCheckBuilder.Add(generator.Assert(f.tok, olderCondition,
            new PODesc.IsOlderProofObligation(olderParameterCount, f.Ins.Count + (f.IsStatic ? 0 : 1))));
        }
      }

      // Combine the two, letting the postcondition be checked on after the "bodyCheckBuilder" branch
      postCheckBuilder.Add(TrAssumeCmd(f.tok, Expr.False));
      builder.Add(new IfCmd(f.tok, null, postCheckBuilder.Collect(f.tok), null, bodyCheckBuilder.Collect(f.tok)));

      var s0 = builderInitializationArea.Collect(f.tok);
      var s1 = builder.Collect(f.tok);
      var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), f.tok);

      if (generator.EmitImplementation(f.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(f.Attributes, null);
        var impl = generator.AddImplementationWithAttributes(generator.GetToken(f), proc,
          Concat(Concat(Bpl.Formal.StripWhereClauses(typeInParams), inParams_Heap), implInParams),
          implOutParams,
          locals, implBody, kv);
        if (generator.InsertChecksums) {
          generator.InsertChecksum(f, impl);
        }
      }

      Contract.Assert(generator.currentModule == f.EnclosingClass.EnclosingModuleDefinition);
      Contract.Assert(generator.codeContext == f);
      generator.Reset();
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

    private List<Ensures> GetWellformnessProcedureEnsures(Function f, ExpressionTranslator etran) {
      var ens = new List<Ensures>();
      foreach (AttributedExpression p in f.Ens) {
        var functionHeight = generator.currentModule.CallGraph.GetSCCRepresentativePredecessorCount(f);
        var splits = new List<SplitExprInfo>();
        bool splitHappened /*we actually don't care*/ =
          generator.TrSplitExpr(p.E, splits, true, functionHeight, true, true, etran);
        var (errorMessage, successMessage) = generator.CustomErrorMessage(p.Attributes);
        foreach (var s in splits) {
          if (s.IsChecked && !RefinementToken.IsInherited(s.Tok, generator.currentModule)) {
            generator.AddEnsures(ens, generator.EnsuresWithDependencies(s.Tok, false, p.E, s.E, errorMessage, successMessage, null));
          }
        }
      }

      return ens;
    }

    private List<Bpl.Requires> GetWellformednessProcedureRequires(Function f, ExpressionTranslator etran,
      Expr prevHeap,
      ExpressionTranslator ordinaryEtran, Expr currHeap) {
      var requires = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      requires.Add(generator.Requires(f.tok, true, null, etran.HeightContext(f), null, null, null));
      if (f is TwoStateFunction) {
        // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
        var a0 = Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
        var a1 = generator.HeapSucc(prevHeap, currHeap);
        var a2 = generator.FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, currHeap);
        requires.Add(generator.Requires(f.tok, true, null, BplAnd(a0, BplAnd(a1, a2)), null, null, null));
      }

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