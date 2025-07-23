using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using DafnyIdentifierExpr = Microsoft.Dafny.IdentifierExpr;
using BoogieIdentifierExpr = Microsoft.Boogie.IdentifierExpr;

namespace Microsoft.Dafny;

public static class OpaqueBlockVerifier {
  public static void EmitBoogie(BoogieGenerator generator, OpaqueBlock block, BoogieStmtListBuilder builder,
    Variables locals, BoogieGenerator.ExpressionTranslator etran, IMethodCodeContext codeContext) {

    var blockBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);

    var bodyTranslator = GetBodyTranslator(generator, block, locals, etran, blockBuilder);
    var prevDefiniteAssignmentTrackers = generator.DefiniteAssignmentTrackers;
    generator.TrStmtList(block.Body, blockBuilder, locals, bodyTranslator, block.EntireRange);
    generator.DefiniteAssignmentTrackers = prevDefiniteAssignmentTrackers;

    var assignedVariables = block.DescendantsAndSelf.
      SelectMany(s => s.GetAssignedLocals()).Select(ie => ie.Var)
      .ToHashSet();
    List<AttributedExpression> totalEnsures = [];

    var variablesUsedInEnsures = block.Ensures.SelectMany(ae => ae.E.DescendantsAndSelf).
      OfType<DafnyIdentifierExpr>().DistinctBy(ie => ie.Var);
    var implicitAssignedIdentifiers =
      variablesUsedInEnsures.Where(v => assignedVariables.Contains(v.Var) && generator.DefiniteAssignmentTrackers.ContainsKey(v.Var.UniqueName));
    foreach (var v in implicitAssignedIdentifiers) {
      var expression = new AttributedExpression(Expression.CreateAssigned(v.Origin, v));
      totalEnsures.Add(expression);
      blockBuilder.Add(generator.Assert(
        v.Origin, etran.TrExpr(expression.E),
        new DefiniteAssignment("variable", v.Var.Name, "here"), builder.Context));
    }

    foreach (var ensure in block.Ensures) {
      totalEnsures.Add(ensure);
      blockBuilder.Add(generator.Assert(
        ensure.Origin, etran.TrExpr(ensure.E),
        new OpaqueEnsuresDescription(), builder.Context,
        etran.TrAttributes(ensure.Attributes, null)));
    }

    BoogieGenerator.ExpressionTranslator beforeBlockExpressionTranslator;
    if (block.Modifies.Expressions.Any()) {
      var context = new OpaqueBlockContext(codeContext, block);
      if (context is IMethodCodeContext methodCodeContext) {
        generator.CheckFrameSubset(
          block.Origin, block.Modifies.Expressions,
          null, null, etran, etran.ModifiesFrame(block.Origin), blockBuilder, new ModifyFrameSubset(
            "opaque block",
            block.Modifies.Expressions,
            methodCodeContext.Modifies.Expressions
          ), null);
      }

      var uniqueId = generator.CurrentIdGenerator.FreshId("$Heap_before_opaque");
      var heapAtVariable = locals.GetOrAdd(new Boogie.LocalVariable(block.Origin,
        new TypedIdent(block.Origin, uniqueId, generator.Predef.HeapType)));
      builder.Add(Cmd.SimpleAssign(block.Origin, new Boogie.IdentifierExpr(block.Origin, heapAtVariable), etran.HeapExpr));

      beforeBlockExpressionTranslator = etran.WithHeapVariable(uniqueId);
    } else {
      beforeBlockExpressionTranslator = etran;
    }

    generator.PathAsideBlock(block.Origin, blockBuilder, builder);

    generator.ApplyModifiesEffect(block, beforeBlockExpressionTranslator, etran, builder, block.Modifies, true, block.IsGhost);
    builder.Add(new HavocCmd(Token.NoToken, assignedVariables.Select(v => new BoogieIdentifierExpr(v.Origin, v.UniqueName)).ToList()));

    foreach (var ensure in totalEnsures) {
      generator.CheckWellformedAndAssume(ensure.E, new WFOptions(null, false),
        locals, builder, etran, null);
    }
  }

  private static BoogieGenerator.ExpressionTranslator GetBodyTranslator(BoogieGenerator generator, OpaqueBlock block, Variables locals,
    BoogieGenerator.ExpressionTranslator etran, BoogieStmtListBuilder blockBuilder) {
    BoogieGenerator.ExpressionTranslator bodyTranslator;
    if (block.Modifies.Expressions.Any()) {
      string modifyFrameName = BoogieGenerator.FrameVariablePrefix + generator.CurrentIdGenerator.FreshId("opaque#");
      generator.DefineFrame(block.Origin, etran.ModifiesFrame(block.Origin), block.Modifies.Expressions, blockBuilder, locals, modifyFrameName);
      bodyTranslator = etran.WithModifiesFrame(modifyFrameName);
    } else {
      bodyTranslator = etran;
    }

    return bodyTranslator;
  }

  class OpaqueEnsuresDescription : ProofObligationDescription {
    public override string SuccessDescription => "ensures always holds";

    public override string FailureDescription => "ensures could not be proved";

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