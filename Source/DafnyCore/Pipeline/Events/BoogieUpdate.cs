using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record BoogieUpdate(ProofDependencyManager ProofDependencyManager,
  ICanVerify CanVerify, IVerificationTask VerificationTask, IVerificationStatus BoogieStatus)
  : ICompilationEvent;

public record PhaseFinished(IPhase Phase) : ICompilationEvent;
public record PhaseStarted(IPhase Phase) : ICompilationEvent;

// Could PhaseFinished replace PhaseDiscovered? Maybe a parent can be finished even when its children are not finished yet.
public record PhaseChildrenDiscovered(IPhase Phase, IReadOnlySet<IPhase> Children) : ICompilationEvent;