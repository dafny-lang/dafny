using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record BoogieUpdate(ICanVerify CanVerify, IImplementationTask ImplementationTask, IVerificationStatus BoogieStatus)
  : ICompilationEvent {

}