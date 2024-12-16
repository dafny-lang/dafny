using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using DafnyIdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using BoogieIdentifierExpr = Microsoft.Boogie.IdentifierExpr;

namespace Microsoft.Dafny;

public static class OpaqueBlockVerifier {
  public static void EmitBoogie(BoogieGenerator generator, OpaqueBlock block, BoogieStmtListBuilder builder,
    Variables locals, BoogieGenerator.ExpressionTranslator etran, IMethodCodeContext codeContext) {

    var hasModifiesClause = block.Modifies.Expressions.Any();
    var blockBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);

    var bodyTranslator = GetBodyTranslator(generator, block, locals, etran, hasModifiesClause, blockBuilder);
    var prevDefiniteAssignmentTrackers = generator.DefiniteAssignmentTrackers;
    generator.TrStmtList(block.Body, blockBuilder, locals, bodyTranslator, block.Origin);
    generator.DefiniteAssignmentTrackers = prevDefiniteAssignmentTrackers;

    var assignedVariables = block.DescendantsAndSelf.
      SelectMany(s => s.GetAssignedLocals()).Select(ie => ie.Var)
      .ToHashSet();
    List<AttributedExpression> totalEnsures = new();

    var variablesUsedInEnsures = block.Ensures.SelectMany(ae => ae.E.DescendantsAndSelf).
      OfType<DafnyIdentifierExpr>().DistinctBy(ie => ie.Var);
    var implicitAssignedIdentifiers =
      variablesUsedInEnsures.Where(v => assignedVariables.Contains(v.Var) && generator.DefiniteAssignmentTrackers.ContainsKey(v.Var.UniqueName));
    foreach (var v in implicitAssignedIdentifiers) {
      var expression = new AttributedExpression(Expression.CreateAssigned(v.Tok, v));
      totalEnsures.Add(expression);
      blockBuilder.Add(generator.Assert(
        v.Tok, etran.TrExpr(expression.E),
        new DefiniteAssignment("variable", v.Var.Name, "here"), builder.Context));
    }

    foreach (var ensure in block.Ensures) {
      totalEnsures.Add(ensure);
      blockBuilder.Add(generator.Assert(
        ensure.Tok, etran.TrExpr(ensure.E),
        new OpaqueEnsuresDescription(), builder.Context,
        etran.TrAttributes(ensure.Attributes, null)));
    }

    if (hasModifiesClause) {
      var context = new OpaqueBlockContext(codeContext, block);
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

  private static BoogieGenerator.ExpressionTranslator GetBodyTranslator(BoogieGenerator generator, OpaqueBlock block, Variables locals,
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