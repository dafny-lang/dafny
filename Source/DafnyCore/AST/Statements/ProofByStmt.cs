namespace Microsoft.Dafny;

class ProofByStmt : Statement, ICanResolveNewAndOld {
  public ProofByStmt(RangeToken range, BlockStmt proof, Statement body) : base(range) {
    Proof = proof;
    Body = body;
  }

  private Statement Body { get; }
  private BlockStmt Proof { get; }

  public override void GenResolve(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    resolver.ResolveStatement(Body, resolutionContext);
    resolver.ResolveBlockStatement(Proof, resolutionContext with {
      CodeContext = new CodeContextWrapper(resolutionContext.CodeContext, true)
    });
    base.GenResolve(resolver, resolutionContext);
  }
}