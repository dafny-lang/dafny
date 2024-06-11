using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record BoogieUpdate(ProofDependencyManager ProofDependencyManager,
  ICanVerify CanVerify, IVerificationTask VerificationTask, IVerificationStatus BoogieStatus)
  : ICompilationEvent {

}