using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny;

// Subclasses of this abstract class implement well-formedness checks for top-level declarations,
// usually for type invariants (initially for class-like declarations, eventually for datatypes, etc.)
// NB: inside Boogie generator to access its private methods
public partial class BoogieGenerator {
  private abstract class TopLevelDeclWellformednessChecker<T>(BoogieGenerator parent, T decl)
    where T : TopLevelDeclWithMembers, ICallable {

    protected readonly Variables Locals = new Variables();
    
    
    // Implements the core logic of a well-formedness check, may delegate reads checks to delayer
    protected abstract void Check(Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      ReadsCheckDelayer delayer);

    protected virtual IEnumerable<Bpl.Requires> Requires() {
      foreach (var typeBoundAxiom in parent.TypeBoundAxioms(decl.Origin, decl.TypeArgs)) {
        yield return parent.Requires(decl.Origin, true, null, typeBoundAxiom, null, null, null);
      }
    }
    
    // NB: mostly copied from FunctionWellformednessChecker.Check
    public void Check() {
      Contract.Assert(parent.InVerificationScope(decl));

      parent.proofDependencies.SetCurrentDefinition($"{decl.FullName} (well-formedness)", decl);
      parent.currentModule = decl.EnclosingModule;
      parent.codeContext = decl;

      var etran = new ExpressionTranslator(parent, parent.Predef, decl.Origin, decl);
      var context = new BodyTranslationContext(false);
      var locals = new Variables();
      var builder = new BoogieStmtListBuilder(parent, parent.options, context);
      var builderInitializationArea = new BoogieStmtListBuilder(parent, parent.options, context);

      // NB: decl.TypeArgs freely occur in type, to be captured by inParams
      var type = UserDefinedType.FromTopLevelDecl(decl.Origin, decl);
      var boogieType = parent.TrType(type);
      var @this = new Bpl.IdentifierExpr(decl.Origin, "this", boogieType);
      var where = BplAnd(parent.ReceiverNotNull(@this), etran.GoodRef(decl.Origin, @this, type));

      List<Bpl.Variable> inParams =
        parent.MkTyParamFormals(decl.TypeArgs, true).Append(
          new Bpl.Formal(decl.Origin, new Bpl.TypedIdent(decl.Origin, "this", boogieType, where), true)
        ).ToList();
      
      var proc = new Bpl.Procedure
      (
        decl.Origin,
        $"CheckWellformed{NameSeparator}{decl.FullName}",
        [],
        inParams,
        [],
        false,
        Requires().ToList(),
        [etran.HeapCastToIdentifierExpr], // TODO do we want this?
        [],
        etran.TrAttributes(decl.Attributes)
      );
      AddVerboseNameAttribute(proc, decl.FullSanitizedName, MethodTranslationKind.SpecWellformedness);
      parent.sink.AddTopLevelDeclaration(proc);
      
      // TODO What does this do?
      builder.AddCaptureState(decl.Origin, false, "initial state");
      List<FrameExpression> reads = [new(decl.Origin, new ThisExpr(decl), null)];
      parent.DefineFrame(decl.Origin, etran.ReadsFrame(decl.Origin), reads, builder, locals, null);
      // TODO do we need fuel?
      parent.InitializeFuelConstant(decl.Origin, builder, etran);

      var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, builder);
      
      // builder.Add(new Bpl.CommentCmd("Assert false 1"));
      // builder.Add(new Bpl.AssertCmd(decl.Origin, Bpl.Expr.False));

      Check(locals, builder, etran, delayer);
      
      // Sanity check, can remove
      builder.Add(new Bpl.CommentCmd("Check well-formedness of the reads clause"));
      delayer.DoWithDelayedReadsChecks(false, wfo => { parent.CheckFrameWellFormed(wfo, reads, locals, builder, etran); });
      
      var implBody = new Bpl.StmtList(new List<Bpl.BigBlock>(
        builderInitializationArea.Collect(decl.Origin).BigBlocks.Concat(
          builder.Collect(decl.Origin).BigBlocks)
        ), decl.Origin);

      parent.AddImplementationWithAttributes(parent.GetToken(decl), proc,
        Bpl.Formal.StripWhereClauses(inParams), [], locals, implBody,
        etran.TrAttributes(decl.Attributes));

      parent.Reset();
    }
  }

  private class ClassLikeDeclWellformednessChecker(BoogieGenerator parent, ClassLikeDecl cls) : TopLevelDeclWellformednessChecker<ClassLikeDecl>(parent, cls) {
    protected override void Check(Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran, ReadsCheckDelayer delayer) {
      // Idea: check-wellformedness-and-assume each invariant. Then, at the end, check that we've only read "this"
      delayer.DoWithDelayedReadsChecks(false, wfo => {
        builder.Add(new Bpl.CommentCmd("Check invariants are well-formed and only read this"));
        foreach (var invariant in ConjunctsOf(cls.Invariants)) {
          parent.CheckWellformedAndAssume(invariant.E, wfo, locals, builder, etran, "invariant");
        }
      });
    }
  }
}