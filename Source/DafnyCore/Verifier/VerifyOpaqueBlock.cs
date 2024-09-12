using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Dafny.ProofObligationDescription;
using Formal = Microsoft.Dafny.Formal;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using IToken = Microsoft.Dafny.IToken;
using ProofObligationDescription = Microsoft.Dafny.ProofObligationDescription.ProofObligationDescription;
using Token = Microsoft.Dafny.Token;

namespace DafnyCore.Verifier;

public static class VerifyOpaqueBlock {
  public static void Translate(BoogieGenerator generator, OpaqueBlock block, BoogieStmtListBuilder builder,
    List<Variable> locals, BoogieGenerator.ExpressionTranslator etran, IMethodCodeContext codeContext) {

    var context = new OpaqueBlockContext(codeContext, block);

    BoogieGenerator.ExpressionTranslator bodyTranslator;
    var hasModifiesClause = block.Modifies.Expressions.Any();
    if (hasModifiesClause) {
      var suffix = generator.CurrentIdGenerator.FreshId("modify#");
      string modifyFrameName = "$Frame$" + suffix;
      generator.DefineFrame(block.Tok, etran.ModifiesFrame(block.Tok), block.Modifies.Expressions, builder, locals, modifyFrameName);
      bodyTranslator = etran.WithModifiesFrame(modifyFrameName);
    } else {
      bodyTranslator = etran;
    }

    IEnumerable<Microsoft.Dafny.IdentifierExpr> assignedVariables;
    //DistinctBy(a => a.Name);

    var implicitEnsures = assignedVariables.Select(v =>
      new AttributedExpression(new UnaryOpExpr(v.Tok, UnaryOpExpr.Opcode.Assigned, v)));
    var totalEnsures = implicitEnsures.Concat(block.Ensures).ToList();
    
    var blockBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);
    foreach (var ensure in totalEnsures) {
      generator.CheckWellformed(ensure.E, new WFOptions(null, false),
        locals, blockBuilder, etran);
    }
    
    var prevDefiniteAssignmentTrackerCount = generator.DefiniteAssignmentTrackers.Count;
    generator.TrStmtList(block.Body, blockBuilder, locals, bodyTranslator, block.RangeToken);
    generator.RemoveDefiniteAssignmentTrackers(block.Body, prevDefiniteAssignmentTrackerCount);
    
    var asserts = totalEnsures.Select(ensures => generator.Assert(
      ensures.Tok, etran.TrExpr(ensures.E),
      new OpaqueEnsuresDescription(),
      etran.TrAttributes(ensures.Attributes, null))).ToList();

    foreach (var assert in asserts) {
      blockBuilder.Add(assert);
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


    blockBuilder.Add(new AssumeCmd(block.Tok, Expr.False));
    var blockCommands = blockBuilder.Collect(block.Tok);
    var ifCmd = new IfCmd(block.Tok, null, blockCommands, null, null);
    builder.Add(ifCmd);

    builder.Add(new HavocCmd(Token.NoToken, assignedVariables.Select(ie => new IdentifierExpr(ie.Tok, ie.Name)).ToList()));

    if (hasModifiesClause) {
      generator.ApplyModifiesEffect(block, etran, builder, block.Modifies, true, block.IsGhost);
    }

    foreach (var assert in asserts) {
      /* It's inefficient to place the ensures clauses in the generated Boogie twice.
       * We could avoid that by adding an OpaqueBlock construct to Boogie
       * Placing the clauses in a function does not seem like an option,
       * because then we would have to add arguments based on the statements preceding this opaque block.
       */
      // TODO missing proof dependency id
      builder.Add(BoogieGenerator.TrAssumeCmd(assert.tok, assert.Expr));
    }
  }

  private static IEnumerable<Cmd> AllCommands(object command) {
    if (command is StmtList stmtList) {
      var prefix = stmtList.PrefixCommands ?? Enumerable.Empty<Cmd>();
      return prefix.Concat(stmtList.BigBlocks.SelectMany(AllCommands));
    }

    if (command is BigBlock bigBlock) {
      return bigBlock.simpleCmds.Concat(AllCommands(bigBlock.ec));
    }
    if (command is WhileCmd whileCmd) {
      return AllCommands(whileCmd.Body);
    }

    if (command is IfCmd ifCmd) {
      return AllCommands(ifCmd.Thn).Concat(AllCommands(ifCmd.ElseBlock));
    }

    if (command is Cmd cmd) {
      return new[] { cmd };
    }

    return Enumerable.Empty<Cmd>();
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