using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private void AddInvariantsWellformednessCheck(Invariant invariant) {
    var decl = invariant.EnclosingClass;
    Contract.Assert(InVerificationScope(invariant));

    proofDependencies.SetCurrentDefinition($"{invariant.FullDafnyName} (well-formedness)", invariant);
    currentModule = decl.EnclosingModuleDefinition;
    codeContext = invariant;

    ExpressionTranslator etran = new(this, Predef, invariant.Origin, invariant);
    BodyTranslationContext context = new(false);
    Variables locals = new();

    var builderInitializationArea = new BoogieStmtListBuilder(this, options, context);
    var builder = new BoogieStmtListBuilder(this, options, context);

    // NB: decl.TypeArgs freely occur in type, to be captured by inParams
    var type = UserDefinedType.FromTopLevelDecl(invariant.Origin, decl);
    var boogieType = TrType(type);
    var @this = new Bpl.IdentifierExpr(invariant.Origin, "this", boogieType);
    var where = BplAnd(ReceiverNotNull(@this), etran.GoodRef(invariant.Origin, @this, type));

    List<Bpl.Variable> inParams =
      MkTyParamFormals(decl.TypeArgs, true).Append(
        new Bpl.Formal(invariant.Origin, new Bpl.TypedIdent(invariant.Origin, "this", boogieType, where), true)
      ).ToList();
    
    IEnumerable<Bpl.Requires> Requires() {
      foreach (var typeBoundAxiom in TypeBoundAxioms(invariant.Origin, decl.TypeArgs)) {
        yield return this.Requires(invariant.Origin, true, null, typeBoundAxiom, null, null, null);
      }
    }

    var proc = new Bpl.Procedure
    (
      invariant.Origin,
      $"CheckWellformed{NameSeparator}{invariant.FullSanitizedName}",
      [],
      inParams,
      [],
      false,
      Requires().ToList(),
      [etran.HeapCastToIdentifierExpr], // TODO(somayyas) do we want this?
      [],
      etran.TrAttributes(invariant.Attributes)
    );
    AddVerboseNameAttribute(proc, invariant.FullSanitizedName, MethodTranslationKind.SpecWellformedness);
    sink.AddTopLevelDeclaration(proc);

    // TODO(somayyas) What does this do?
    builder.AddCaptureState(invariant.Origin, false, "initial state");
    List<FrameExpression> reads = [new(invariant.Origin, new ThisExpr(invariant), null)];
    DefineFrame(invariant.Origin, etran.ReadsFrame(invariant.Origin), reads, builder, locals, null);
    // TODO(somayyas) do we need fuel?
    InitializeFuelConstant(invariant.Origin, builder, etran);

    var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, builder);
    
    // Idea: check-wellformedness-and-assume each invariant. Then, at the end, check that we've only read "this"
    delayer.DoWithDelayedReadsChecks(false, wfo => {
      builder.Add(new Bpl.CommentCmd("Check invariants are well-formed and only read this"));
      foreach (var clause in ConjunctsOf(invariant.Body)) {
        CheckWellformedAndAssume(clause.E, wfo, locals, builder, etran, "invariant");
      }
    });
    
    // Sanity check
    builder.Add(new Bpl.CommentCmd("Check well-formedness of the reads clause"));
    delayer.DoWithDelayedReadsChecks(false, wfo => { CheckFrameWellFormed(wfo, reads, locals, builder, etran); });

    var implBody = new Bpl.StmtList(new List<Bpl.BigBlock>(
      builderInitializationArea.Collect(invariant.Origin).BigBlocks.Concat(
        builder.Collect(invariant.Origin).BigBlocks)
    ), invariant.Origin);

    AddImplementationWithAttributes(GetToken(invariant), proc,
      Bpl.Formal.StripWhereClauses(inParams), [], locals, implBody,
      etran.TrAttributes(invariant.Attributes));

    Reset();
  }
}