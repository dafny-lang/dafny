using System;
using System.Collections.Generic;
using System.IO;

namespace Microsoft.Dafny;

public class BlockByProofStmt : Statement, ICanResolveNewAndOld, ICanPrint,
  ICloneable<Statement>, ICanFormat {

  public Statement Body { get; }
  public BlockStmt Proof { get; }
  public BlockByProofStmt(IOrigin range, BlockStmt proof, Statement body) : base(range) {
    Proof = proof;
    Body = body;
  }
  public BlockByProofStmt(Cloner cloner, BlockByProofStmt original) : base(cloner, original) {
    Proof = cloner.CloneBlockStmt(original.Proof);
    Body = cloner.CloneStmt(original.Body, false);
  }

  public override IEnumerable<Statement> SubStatements => new[] { Body, Proof };

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveStatement(Body, resolutionContext);
    ResolveByProof(resolver, Proof, resolutionContext);
    base.GenResolve(resolver, resolutionContext);
  }

  internal static void ResolveByProof(INewOrOldResolver resolver, BlockStmt proof, ResolutionContext resolutionContext) {
    if (proof == null) {
      return;
    }

    // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave the proof body
    var prevLblStmts = resolver.EnclosingStatementLabels;
    var prevLoopStack = resolver.LoopStack;
    resolver.EnclosingStatementLabels = new Scope<Statement>(resolver.Options);
    resolver.LoopStack = new List<Statement>();
    resolver.ResolveStatement(proof, resolutionContext);
    resolver.EnclosingStatementLabels = prevLblStmts;
    resolver.LoopStack = prevLoopStack;
  }

  public void Render(TextWriter wr, Printer printer, int indent) {
    printer.PrintStatement(Body, indent, false);
    wr.Write(" by ");
    printer.PrintBlockStmt(Proof, indent);
  }

  public Statement Clone(Cloner cloner) {
    return new BlockByProofStmt(cloner, this);
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext, string proofContext,
    bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    IsGhost = mustBeErasable;  // set .IsGhost before descending into substatements (since substatements may do a 'break' out of this block)
    Body.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext, proofContext, allowAssumptionVariables, inConstructorInitializationPhase);
    IsGhost = IsGhost || Body.IsGhost;

    Proof.ResolveGhostness(resolver, reporter, true, codeContext, "a by block", allowAssumptionVariables, inConstructorInitializationPhase);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    formatter.SetStatementIndentation(Body);
    Proof.SetIndent(indentBefore, formatter);
    return false;
  }
}