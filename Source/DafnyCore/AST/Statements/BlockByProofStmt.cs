namespace Microsoft.Dafny;

public class BlockByProofStmt : Statement, ICanResolveNewAndOld {
  public BlockByProofStmt(RangeToken range, BlockStmt proof, Statement body) : base(range) {
    Proof = proof;
    Body = body;
  }

  public Statement Body { get; }
  public BlockStmt Proof { get; }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveStatement(Body, resolutionContext);
    resolver.ResolveBlockStatement(Proof, resolutionContext with {
      CodeContext = new CodeContextWrapper(resolutionContext.CodeContext, true)
    });
    base.GenResolve(resolver, resolutionContext);
  }
}