using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VCGeneration.Splits;
using ExistsExpr = Microsoft.Dafny.ExistsExpr;

namespace DafnyCore.Verifier.Statements;

public class IfStatementVerifier {

  public static void EmitBoogie(BoogieGenerator generator, IfStmt stmt, BoogieStmtListBuilder builder,
    Variables locals, BoogieGenerator.ExpressionTranslator etran) {
    Contract.Requires(stmt != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);

    BoogieGenerator.AddComment(builder, stmt, "if statement");
    Expression guard;
    if (stmt.Guard == null) {
      guard = null;
    } else {
      guard = stmt.IsBindingGuard ? ((ExistsExpr)stmt.Guard).AlphaRename("eg$") : stmt.Guard;
      generator.TrStmt_CheckWellformed(guard, builder, locals, etran, true);
    }
    var thenBuilder = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    if (stmt.IsBindingGuard) {
      generator.CurrentIdGenerator.Push();
      var exists = (ExistsExpr)stmt.Guard; // the original (that is, not alpha-renamed) guard
      generator.IntroduceAndAssignExistentialVars(exists, thenBuilder, builder, locals, etran, stmt.IsGhost);
      generator.CurrentIdGenerator.Pop();
    }
    generator.CurrentIdGenerator.Push();
    StmtList thenList = generator.TrStmt2StmtList(thenBuilder, stmt.Thn, locals, etran, stmt.Thn is not BlockStmt);
    generator.CurrentIdGenerator.Pop();
    StmtList elseList;
    IfCmd elseIf = null;
    var elseBuilder = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    if (stmt.IsBindingGuard) {
      elseBuilder.Add(generator.TrAssumeCmdWithDependenciesAndExtend(etran, guard.Tok, guard, Expr.Not, "if statement binding guard"));
    }
    if (stmt.Els == null) {
      elseList = elseBuilder.Collect(stmt.Tok);
    } else {
      generator.CurrentIdGenerator.Push();
      elseList = generator.TrStmt2StmtList(elseBuilder, stmt.Els, locals, etran, stmt.Els is not BlockStmt);
      generator.CurrentIdGenerator.Pop();
      if (elseList.BigBlocks.Count == 1) {
        BigBlock bb = elseList.BigBlocks[0];
        if (bb.LabelName == null && bb.simpleCmds.Count == 0 && bb.ec is IfCmd ec) {
          elseIf = ec;
          elseList = null;
        }
      }
    }
    builder.Add(new IfCmd(stmt.Tok,
      guard == null || stmt.IsBindingGuard ? null : etran.TrExpr(guard),
      thenList, elseIf, elseList, BlockRewriter.AllowSplitQ));
  }
}