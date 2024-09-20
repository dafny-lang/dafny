using System.Collections.Generic;

namespace Microsoft.Dafny;

public class BlockByProofStmt : Statement, ICanResolveNewAndOld {
  public BlockByProofStmt(RangeToken range, BlockStmt proof, Statement body) : base(range) {
    Proof = proof;
    Body = body;
  }

  public Statement Body { get; }
  public BlockStmt Proof { get; }

  public override IEnumerable<Statement> SubStatements => new[] { Body, Proof };

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveStatement(Body, resolutionContext);
    ResolveByProof(resolver, Proof, resolutionContext with {
      CodeContext = new CodeContextWrapper(resolutionContext.CodeContext, true)
    });
    base.GenResolve(resolver, resolutionContext);
  }

  // CheckLocalityUpdates

  // GhostInterestVisitor
  // if (s.Proof != null) {
  //   Visit(s.Proof, true, "a call-by body");
  // }

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
}