using System.Diagnostics.Contracts;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class IfStatementVerifier {
  public static void EmitBoogie(BoogieGenerator generator, IfStmt stmt, BoogieStmtListBuilder builder, Variables locals, BoogieGenerator.ExpressionTranslator etran) {
    Contract.Requires(stmt != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);

    generator.AddComment(builder, stmt, "if statement");
    Expression guard;
    if (stmt.Guard == null) {
      guard = null;
    } else {
      guard = stmt.IsBindingGuard ? ((ExistsExpr)stmt.Guard).AlphaRename("eg$") : stmt.Guard;
      generator.TrStmt_CheckWellformed(guard, builder, locals, etran, true);
    }
    BoogieStmtListBuilder b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    if (stmt.IsBindingGuard) {
      generator.CurrentIdGenerator.Push();
      var exists = (ExistsExpr)stmt.Guard; // the original (that is, not alpha-renamed) guard
      generator.IntroduceAndAssignExistentialVars(exists, b, builder, locals, etran, stmt.IsGhost);
      generator.CurrentIdGenerator.Pop();
    }

    generator.CurrentIdGenerator.Push();
    Boogie.StmtList thn = generator.TrStmt2StmtList(b, stmt.Thn, locals, etran, stmt.Thn is not BlockStmt);
    generator.CurrentIdGenerator.Pop();
    Boogie.StmtList els;
    Boogie.IfCmd elsIf = null;
    b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    if (stmt.IsBindingGuard) {
      b.Add(generator.TrAssumeCmdWithDependenciesAndExtend(etran, guard.tok, guard, Expr.Not, "if statement binding guard"));
    }
    if (stmt.Els == null) {
      els = b.Collect(stmt.Tok);
    } else {
      generator.CurrentIdGenerator.Push();
      els = generator.TrStmt2StmtList(b, stmt.Els, locals, etran, stmt.Els is not BlockStmt);
      generator.CurrentIdGenerator.Pop();
      if (els.BigBlocks.Count == 1) {
        Boogie.BigBlock bb = els.BigBlocks[0];
        if (bb.LabelName == null && bb.simpleCmds.Count == 0 && bb.ec is Boogie.IfCmd) {
          elsIf = (Boogie.IfCmd)bb.ec;
          els = null;
        }
      }
    }
    builder.Add(new Boogie.IfCmd(stmt.Tok, guard == null || stmt.IsBindingGuard ? null : etran.TrExpr(guard), thn, elsIf, els));
  }
}