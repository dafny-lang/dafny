using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.ProofObligationDescription;
using Formal = Microsoft.Dafny.Formal;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using ProofObligationDescription = Microsoft.Dafny.ProofObligationDescription.ProofObligationDescription;
using Token = Microsoft.Dafny.Token;

namespace DafnyCore.Verifier;

public static class OpaqueBlockVerifier {
  public static void EmitBoogie(BoogieGenerator generator, OpaqueBlock block, BoogieStmtListBuilder builder,
    List<Variable> locals, BoogieGenerator.ExpressionTranslator etran, IMethodCodeContext codeContext) {

    var context = new OpaqueBlockContext(codeContext, block);

    BoogieGenerator.ExpressionTranslator bodyTranslator;
    var hasModifiesClause = block.Modifies.Expressions.Any();
    if (hasModifiesClause) {
      string modifyFrameName = BoogieGenerator.FrameVariablePrefix + generator.CurrentIdGenerator.FreshId("opaque#");
      generator.DefineFrame(block.Tok, etran.ModifiesFrame(block.Tok), block.Modifies.Expressions, builder, locals, modifyFrameName);
      bodyTranslator = etran.WithModifiesFrame(modifyFrameName);
    } else {
      bodyTranslator = etran;
    }

    var assignedVariables = block.DescendantsAndSelf.
      SelectMany(s => s.GetAssignedLocals()).DistinctBy(ie => ie.Var)
      .ToList();

    var implicitEnsures = assignedVariables.Where(
      v => generator.DefiniteAssignmentTrackers.ContainsKey(v.Var.UniqueName)).Select(v =>
      new AttributedExpression(Expression.CreateAssigned(v.Tok, v)));
    var totalEnsures = implicitEnsures.Concat(block.Ensures).ToList();
    
    var blockBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);
    
    var prevDefiniteAssignmentTrackerCount = generator.DefiniteAssignmentTrackers.Count;
    generator.TrStmtList(block.Body, blockBuilder, locals, bodyTranslator, block.RangeToken);
    generator.RemoveDefiniteAssignmentTrackers(block.Body, prevDefiniteAssignmentTrackerCount);

    foreach (var ensure in totalEnsures) {
      blockBuilder.Add(generator.Assert(
        ensure.Tok, etran.TrExpr(ensure.E),
        new OpaqueEnsuresDescription(),
        etran.TrAttributes(ensure.Attributes, null)));
    }

    if (hasModifiesClause) {
      if (context is IMethodCodeContext methodCodeContext) {
        // We do this modifies check inside the already isolated block
        // TODO combine this part with the CheckFrameSubset check from method calls
        var desc = new ModifyFrameSubset(
          "opaque block",
          block.Modifies.Expressions,
          methodCodeContext.Modifies.Expressions
        );
        generator.CheckFrameSubset(
          block.Tok, block.Modifies.Expressions,
          null, null, etran, etran.ModifiesFrame(block.Tok), blockBuilder, desc, null);
      }
    }
    
    generator.PathAsideBlock(block.Tok, blockBuilder, builder);
    builder.Add(new HavocCmd(Token.NoToken, assignedVariables.Select(ie => new IdentifierExpr(ie.Tok, ie.Var.UniqueName)).ToList()));

    if (hasModifiesClause) {
      generator.ApplyModifiesEffect(block, etran, builder, block.Modifies, true, block.IsGhost);
    }

    foreach (var ensure in totalEnsures) {
      generator.CheckWellformedAndAssume(ensure.E, new WFOptions(null, false),
        locals, builder, etran, null);
    }
  }

  class OpaqueEnsuresDescription : ProofObligationDescription {
    public override string SuccessDescription => "ensures always holds";

    public override string FailureDescription => "ensures might not hold";

    public override string ShortDescription => "opaque block ensure clause";
    public override bool IsImplicit => false;
  }

  class OpaqueBlockContext : CallableWrapper, IMethodCodeContext {
    private readonly IMethodCodeContext callable;
    private readonly OpaqueBlock opaqueBlock;

    public OpaqueBlockContext(IMethodCodeContext callable, OpaqueBlock opaqueBlock)
      : base(callable, callable.IsGhost) {
      this.callable = callable;
      this.opaqueBlock = opaqueBlock;
    }

    public List<Formal> Outs => callable.Outs;

    public Specification<FrameExpression> Modifies => opaqueBlock.Modifies;
  }
}