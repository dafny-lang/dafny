using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {

    private void TrPredicateStmt(PredicateStmt stmt, BoogieStmtListBuilder builder,
      Variables locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Origin, fuelContext, reporter);
      if (stmt is AssertStmt || options.DisallowSoundnessCheating) {
        TrAssertStmt(stmt, builder, locals, etran);
      } else if (stmt is ExpectStmt expectStmt) {
        TrExpectStmt(builder, locals, etran, expectStmt);
      } else if (stmt is AssumeStmt assumeStmt) {
        TrAssumeStmt(assumeStmt, builder, locals, etran);
      }
      fuelContext = FuelSetting.PopFuelContext();
    }

    private void TrAssumeStmt(AssumeStmt assumeStmt, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
      AddComment(builder, assumeStmt, "assume statement");
      stmtContext = StmtType.ASSUME;
      TrStmt_CheckWellformed(assumeStmt.Expr, builder, locals, etran, false);
      builder.Add(TrAssumeCmdWithDependencies(etran, assumeStmt.Origin, assumeStmt.Expr, "assume statement", true,
        etran.TrAttributes(assumeStmt.Attributes, null)));
      stmtContext = StmtType.NONE; // done with translating assume stmt.
      if (options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        builder.AddCaptureState(assumeStmt);
      }
    }

    private void TrExpectStmt(BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran, ExpectStmt expectStmt) {
      AddComment(builder, expectStmt, "expect statement");
      stmtContext = StmtType.ASSUME;
      TrStmt_CheckWellformed(expectStmt.Expr, builder, locals, etran, false);

      // Need to check the message is well-formed, assuming the expected expression
      // does NOT hold:
      //
      // if Not(TrExpr[[ s.Expr ]]) {
      //  CheckWellformed[[ s.Message ]]
      //  assume false;
      // }
      BoogieStmtListBuilder thnBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
      TrStmt_CheckWellformed(expectStmt.Message, thnBuilder, locals, etran, false);
      thnBuilder.Add(TrAssumeCmd(expectStmt.Origin, new Bpl.LiteralExpr(expectStmt.Origin, false),
        etran.TrAttributes(expectStmt.Attributes, null)));
      Bpl.StmtList thn = thnBuilder.Collect(expectStmt.Origin);
      builder.Add(new Bpl.IfCmd(expectStmt.Origin, Bpl.Expr.Not(etran.TrExpr(expectStmt.Expr)), thn, null, null));

      stmtContext = StmtType.NONE; // done with translating expect stmt.
    }

    public void TrAssertStmt(PredicateStmt stmt, BoogieStmtListBuilder builder, Variables locals,
      ExpressionTranslator etran) {
      var stmtBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
      var defineFuel = DefineFuelConstant(stmt.Origin, stmt.Attributes, stmtBuilder, etran);
      var b = defineFuel ? stmtBuilder : builder;
      stmtContext = StmtType.ASSERT;
      AddComment(b, stmt, "assert statement");
      TrStmt_CheckWellformed(stmt.Expr, b, locals, etran, false);

      var hiddenProof = false;
      BoogieStmtListBuilder proofBuilder = null;
      var assertStmt = stmt as AssertStmt;
      if (assertStmt is { Label: not null }) {
        hiddenProof = true;
        proofBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
        AddComment(proofBuilder, stmt, "assert statement proof");
      }
      proofBuilder ??= b;

      var splitHappened = TrAssertCondition(stmt, etran, proofBuilder);

      if (hiddenProof) {
        PathAsideBlock(stmt.Origin, proofBuilder, b);
      }

      stmtContext = StmtType.NONE; // done with translating assert stmt
      if (splitHappened || hiddenProof) {
        if (assertStmt is { Label: not null }) {
          // make copies of the variables used in the assertion
          var name = "$Heap_at_" + assertStmt.Label.AssignUniqueId(CurrentIdGenerator);
          var heapAt = locals.GetOrAdd(new Bpl.LocalVariable(stmt.Origin, new Bpl.TypedIdent(stmt.Origin, name, Predef.HeapType)));
          var heapReference = new Bpl.IdentifierExpr(stmt.Origin, heapAt);
          b.Add(Bpl.Cmd.SimpleAssign(stmt.Origin, heapReference, etran.HeapExpr));
          var substMap = new Dictionary<IVariable, Expression>();
          foreach (var v in FreeVariablesUtil.ComputeFreeVariables(options, assertStmt.Expr)) {
            if (v is LocalVariable) {
              var vcopy = new LocalVariable(stmt.Origin, string.Format("##{0}#{1}", name, v.Name), v.Type,
                v.IsGhost);
              vcopy.type = vcopy.SafeSyntacticType; // resolve local here
              IdentifierExpr ie = new IdentifierExpr(vcopy.Origin,
                vcopy.AssignUniqueName(CurrentDeclaration.IdGenerator));
              ie.Var = vcopy;
              ie.Type = ie.Var.Type; // resolve ie here
              substMap.Add(v, ie);
              locals.GetOrAdd(new Bpl.LocalVariable(vcopy.Origin,
                new Bpl.TypedIdent(vcopy.Origin, vcopy.AssignUniqueName(CurrentDeclaration.IdGenerator),
                  TrType(vcopy.Type))));
              b.Add(Bpl.Cmd.SimpleAssign(stmt.Origin, TrVar(stmt.Origin, vcopy), TrVar(stmt.Origin, v)));
            }
          }

          var exprToBeRevealed = Substitute(assertStmt.Expr, null, substMap);
          var etr = new ExpressionTranslator(etran, heapReference);
          assertStmt.Label.E = etr.TrExpr(exprToBeRevealed);
        } else if (!defineFuel) {
          // Adding the assume stmt, resetting the stmtContext
          stmtContext = StmtType.ASSUME;
          adjustFuelForExists = true;
          b.Add(TrAssumeCmdWithDependencies(etran, stmt.Origin, stmt.Expr, "assert statement", true));
          stmtContext = StmtType.NONE;
        }
      }

      if (defineFuel) {
        var ifCmd = new Bpl.IfCmd(stmt.Origin, null, b.Collect(stmt.Origin), null,
          null); // BUGBUG: shouldn't this first append "assume false" to "b"? (use PathAsideBlock to do this)  --KRML
        builder.Add(ifCmd);
        // Adding the assume stmt, resetting the stmtContext
        stmtContext = StmtType.ASSUME;
        adjustFuelForExists = true;
        builder.Add(TrAssumeCmdWithDependencies(etran, stmt.Origin, stmt.Expr, "assert statement", true));
        stmtContext = StmtType.NONE;
      }

      if (options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        builder.AddCaptureState(stmt);
      }
    }

    private bool TrAssertCondition(PredicateStmt stmt,
      ExpressionTranslator etran, BoogieStmtListBuilder proofBuilder) {

      var (errorMessage, successMessage) = CustomErrorMessage(stmt.Attributes);
      var splits = TrSplitExpr(proofBuilder.Context, stmt.Expr, etran, true, out var splitHappened);
      if (!splitHappened) {
        var desc = new AssertStatementDescription(stmt, errorMessage, successMessage);
        proofBuilder.Add(Assert(stmt.Origin, etran.TrExpr(stmt.Expr), desc, stmt.Origin, proofBuilder.Context,
          etran.TrAttributes(stmt.Attributes, null)));
      } else {
        foreach (var split in splits) {
          if (split.IsChecked) {
            var tok = split.E.tok;
            var desc = new AssertStatementDescription(stmt, errorMessage, successMessage);
            proofBuilder.Add(AssertAndForget(proofBuilder.Context, ToDafnyToken(tok), split.E, desc, stmt.Origin,
              etran.TrAttributes(stmt.Attributes, null))); // attributes go on every split
          }
        }
      }

      return splitHappened;
    }
  }
}