using Microsoft.Dafny;

namespace Microsoft.Dafny;

public class BlockByProofStmtVerifier {
  public static void EmitBoogie(BoogieGenerator generator, BlockByProofStmt block, BoogieStmtListBuilder builder,
    Variables locals, BoogieGenerator.ExpressionTranslator etran, ICodeContext codeContext) {
    var proofBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);

    var previousTrackers = generator.DefiniteAssignmentTrackers;
    generator.CurrentIdGenerator.Push();
    generator.TrStmtList(block.Proof.Body, proofBuilder, locals, etran);
    generator.CurrentIdGenerator.Pop();
    generator.DefiniteAssignmentTrackers = previousTrackers;

    generator.TrStmt(block.Body, proofBuilder, locals, etran);

    generator.PathAsideBlock(block.Origin, proofBuilder, builder);
    generator.TrStmt(block.Body, builder.WithContext(builder.Context with {
      AssertMode = AssertMode.Assume
    }), locals, etran);

  }
}