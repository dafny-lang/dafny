using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// A statement something like a try/catch block that recovers from halting.
/// Not actually useable in Dafny syntax, but would likely look something like this if it was:
///
/// try {
///   <Body>
/// } recover (haltMessage: string) {
///   <RecoveryBlock>
/// }
///
/// </summary>
public class TryRecoverStatement : Statement, ICloneable<TryRecoverStatement> {
  public Statement TryBody;
  public IVariable HaltMessageVar;
  public Statement RecoverBody;

  public TryRecoverStatement Clone(Cloner cloner) {
    return new TryRecoverStatement(cloner, this);
  }

  public TryRecoverStatement(Cloner cloner, TryRecoverStatement original) : base(cloner, original) {
    TryBody = cloner.CloneStmt(original.TryBody, false);
    RecoverBody = cloner.CloneStmt(original.RecoverBody, false);
    HaltMessageVar = cloner.CloneIVariable(original.HaltMessageVar, false);
  }

  public TryRecoverStatement(Statement tryBody, IVariable haltMessageVar, Statement recoverBody)
    : base(new SourceOrigin(tryBody.StartToken, recoverBody.EndToken)) {
    Contract.Requires(tryBody != null);
    Contract.Requires(haltMessageVar != null);
    Contract.Requires(recoverBody != null);
    TryBody = tryBody;
    HaltMessageVar = haltMessageVar;
    RecoverBody = recoverBody;
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable, ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    throw new System.NotSupportedException("This type is only created after resolution");
  }
}