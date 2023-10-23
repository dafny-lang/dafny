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
  public readonly Statement TryBody;
  public readonly IVariable HaltMessageVar;
  public readonly Statement RecoverBody;

  public TryRecoverStatement Clone(Cloner cloner) {
    return new TryRecoverStatement(cloner, this);
  }

  public TryRecoverStatement(Cloner cloner, TryRecoverStatement original) : base(cloner, original) {
    TryBody = cloner.CloneStmt(original.TryBody);
    RecoverBody = cloner.CloneStmt(original.RecoverBody);
    HaltMessageVar = cloner.CloneIVariable(original.HaltMessageVar, false);
  }

  public TryRecoverStatement(Statement tryBody, IVariable haltMessageVar, Statement recoverBody)
    : base(new RangeToken(tryBody.StartToken, recoverBody.EndToken)) {
    Contract.Requires(tryBody != null);
    Contract.Requires(haltMessageVar != null);
    Contract.Requires(recoverBody != null);
    TryBody = tryBody;
    HaltMessageVar = haltMessageVar;
    RecoverBody = recoverBody;
  }
}