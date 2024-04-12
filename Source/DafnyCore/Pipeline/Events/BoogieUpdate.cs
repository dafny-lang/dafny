using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record BoogieUpdate(ProofDependencyManager ProofDependencyManager,
  ICanVerify CanVerify, IVerificationTask VerificationTask, IVerificationStatus BoogieStatus)
  : ICompilationEvent {

}

public record PhaseFinished(IPhase Phase) : ICompilationEvent;
public record PhaseStarted(IPhase Phase) : ICompilationEvent;
public record PhaseDiscovered(IPhase Phase, IReadOnlyList<IPhase> Children) : ICompilationEvent;