#nullable enable
using System;
using System.Collections.Generic;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

/// <summary>
/// Orders phases by their start time.
/// Reports diagnostics only after all phases that come before the phase of this diagnostics, have finished.
/// </summary>
class PhaseOrderedDiagnosticsReporter : IDiagnosticsReporter {
  private ILogger logger;
  private readonly Action<NewDiagnostic> processNewDiagnostic;
  private readonly Dictionary<IPhase, PhaseState> state = new();
  private PhaseState? currentPhase;
  private readonly object myLock = new();

  public PhaseOrderedDiagnosticsReporter(Action<NewDiagnostic> processNewDiagnostic, ILogger logger) {
    this.processNewDiagnostic = processNewDiagnostic;
    this.logger = logger;
  }


  public void PhaseStart(IPhase phase) {
    lock (myLock) {
      var newPhaseState = new PhaseState(currentPhase, phase);
      if (currentPhase != null) {
        currentPhase.Next = newPhaseState;
      }
      state[phase] = newPhaseState;
      currentPhase = newPhaseState;
    }
  }

  public void PhaseFinished(IPhase phase) {
    lock (myLock) {
      if (!state.TryGetValue(phase, out var phaseState)) {
        phaseState = new PhaseState(currentPhase, phase);
        state[phase] = phaseState;
      }
      phaseState.Finish(processNewDiagnostic);
    }
  }

  public void NewDiagnostic(NewDiagnostic newDiagnostic) {
    lock (myLock) {
      var phase = newDiagnostic.Diagnostic.Phase;
      PhaseState? phaseState = null;
      while (phase != null && !state.TryGetValue(phase, out phaseState)) {
        phase = phase.MaybeParent;
      }

      if (phaseState == null) {
        PhaseStart(newDiagnostic.Diagnostic.Phase);
        NewDiagnostic(newDiagnostic);

      } else {
        if (phaseState.Published) {
          processNewDiagnostic(newDiagnostic);
        } else {
          phaseState.QueuedDiagnostics.Enqueue(newDiagnostic);
        }
      }
    }
  }
}

class PhaseState {
  public IPhase Phase;
  public PhaseState? Previous { get; }
  public PhaseState? Next { get; set; }

  public Queue<NewDiagnostic> QueuedDiagnostics { get; } = new();

  public bool Finished { get; set; }
  public bool Published { get; set; }

  public PhaseState(PhaseState? previous, IPhase phase) {
    Previous = previous;
    Phase = phase;
  }

  public IEnumerable<IPhase> Lefts {
    get {
      yield return Phase;
      if (Previous == null) {
        yield break;
      }

      foreach (var l in Previous.Lefts) {
        yield return l;
      }
    }
  }

  public IEnumerable<IPhase> Rights {
    get {
      yield return Phase;
      if (Next == null) {
      } else {
        foreach (var r in Next.Rights) {
          yield return r;
        }
      }
    }
  }

  public void Finish(Action<NewDiagnostic> processNewDiagnostic) {
    Finished = true;
    if (Previous is { Published: false }) {
      return;
    }

    var phaseToPublish = this;
    while (phaseToPublish is { Finished: true }) {
      phaseToPublish.Published = true;
      foreach (var diagnostic in phaseToPublish.QueuedDiagnostics) {
        processNewDiagnostic(diagnostic);
      }

      phaseToPublish = phaseToPublish.Next;
    }
  }
}
