using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Dafny;

namespace DafnyCore.Verifier.Statements;

public class BlockByProofStmtVerifier {
  public static void EmitBoogie(BoogieGenerator generator, BlockByProofStmt block, BoogieStmtListBuilder builder,
    List<Variable> locals, BoogieGenerator.ExpressionTranslator etran, ICodeContext codeContext) {
    var proofBuilder = new BoogieStmtListBuilder(generator, builder.Options, builder.Context);
    generator.TrStmtList(block.Proof.Body, proofBuilder, locals, etran);
    generator.TrStmt(block.Body, proofBuilder, locals, etran);
    generator.PathAsideBlock(block.Tok, proofBuilder, builder);
    generator.TrStmt(block.Body, builder.WithContext(builder.Context with {
      AssertMode = AssertMode.Assume
    }), locals, etran);
  }
}