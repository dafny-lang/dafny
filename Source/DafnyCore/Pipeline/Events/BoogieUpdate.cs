using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record BoogieUpdate(ProofDependencyManager ProofDependencyManager,
  ICanVerify CanVerify, IImplementationTask ImplementationTask, IVerificationStatus BoogieStatus)
  : ICompilationEvent {

}