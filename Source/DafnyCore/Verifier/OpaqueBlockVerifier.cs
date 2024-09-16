using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.ProofObligationDescription;
using Formal = Microsoft.Dafny.Formal;
using DafnyIdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using BoogieIdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using ProofObligationDescription = Microsoft.Dafny.ProofObligationDescription.ProofObligationDescription;
using Token = Microsoft.Dafny.Token;

namespace DafnyCore.Verifier;

public static class OpaqueBlockVerifier {
  public static void EmitBoogie(BoogieGenerator generator, OpaqueBlock block, BoogieStmtListBuilder builder,
    List<Variable> locals, BoogieGenerator.ExpressionTranslator etran, IMethodCodeContext codeContext) {

    var context = new OpaqueBlockContext(codeContext, block);

    var hasModifiesClause = block.Modifies.Expressions.Any();


    var blockBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);

    var bodyTranslator = GetBodyTranslator(generator, block, locals, etran, hasModifiesClause, blockBuilder);
    var prevDefiniteAssignmentTrackerCount = generator.DefiniteAssignmentTrackers.Count;
    generator.TrStmtList(block.Body, blockBuilder, locals, bodyTranslator, block.RangeToken);
    generator.RemoveDefiniteAssignmentTrackers(block.Body, prevDefiniteAssignmentTrackerCount);

    var assignedVariables = block.DescendantsAndSelf.
      SelectMany(s => s.GetAssignedLocals()).Select(ie => ie.Var)
      .ToHashSet();
    List<AttributedExpression> totalEnsures = new();

    var variablesUsedInEnsures = block.Ensures.SelectMany(ae => ae.E.DescendantsAndSelf).
      OfType<DafnyIdentifierExpr>().DistinctBy(ie => ie.Var);
    var implicitAssignedIdentifiers = variablesUsedInEnsures.Where(
      v => assignedVariables.Contains(v.Var) && generator.DefiniteAssignmentTrackers.ContainsKey(v.Var.UniqueName));
    foreach (var v in implicitAssignedIdentifiers) {
      var expression = new AttributedExpression(Expression.CreateAssigned(v.Tok, v));
      totalEnsures.Add(expression);
      blockBuilder.Add(generator.Assert(
        v.Tok, etran.TrExpr(expression.E),
        new DefiniteAssignment("variable", v.Var.Name, "here")));
    }

    foreach (var ensure in block.Ensures) {
      totalEnsures.Add(ensure);
      blockBuilder.Add(generator.Assert(
        ensure.Tok, etran.TrExpr(ensure.E),
        new OpaqueEnsuresDescription(),
        etran.TrAttributes(ensure.Attributes, null)));
    }

    if (hasModifiesClause) {
      if (context is IMethodCodeContext methodCodeContext) {
        generator.CheckFrameSubset(
          block.Tok, block.Modifies.Expressions,
          null, null, etran, etran.ModifiesFrame(block.Tok), blockBuilder, new ModifyFrameSubset(
            "opaque block",
            block.Modifies.Expressions,
            methodCodeContext.Modifies.Expressions
          ), null);
      }
    }

    generator.PathAsideBlock(block.Tok, blockBuilder, builder);
    builder.Add(new HavocCmd(Token.NoToken, assignedVariables.Select(v => new BoogieIdentifierExpr(v.Tok, v.UniqueName)).ToList()));

    if (hasModifiesClause) {
      generator.ApplyModifiesEffect(block, etran, builder, block.Modifies, true, block.IsGhost);
    }

    foreach (var ensure in totalEnsures) {
      generator.CheckWellformedAndAssume(ensure.E, new WFOptions(null, false),
        locals, builder, etran, null);
    }
  }

  private static BoogieGenerator.ExpressionTranslator GetBodyTranslator(BoogieGenerator generator, OpaqueBlock block, List<Variable> locals,
    BoogieGenerator.ExpressionTranslator etran, bool hasModifiesClause, BoogieStmtListBuilder blockBuilder) {
    BoogieGenerator.ExpressionTranslator bodyTranslator;
    if (hasModifiesClause) {
      string modifyFrameName = BoogieGenerator.FrameVariablePrefix + generator.CurrentIdGenerator.FreshId("opaque#");
      generator.DefineFrame(block.Tok, etran.ModifiesFrame(block.Tok), block.Modifies.Expressions, blockBuilder, locals, modifyFrameName);
      bodyTranslator = etran.WithModifiesFrame(modifyFrameName);
    } else {
      bodyTranslator = etran;
    }

    return bodyTranslator;
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