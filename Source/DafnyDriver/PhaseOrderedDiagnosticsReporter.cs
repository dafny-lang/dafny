#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Reactive;
using Microsoft.Dafny;

namespace DafnyDriver.Commands;

/// <summary>
/// Orders phases by their start time.
/// Reports diagnostics only after all phases that come before the phase of this diagnostics, have finished.
/// </summary>
class PhaseOrderedDiagnosticsReporter {
  private readonly Action<NewDiagnostic> processNewDiagnostic;
  private readonly ConcurrentDictionary<IPhase, IPhase> previousPhases = new();
  private readonly ConcurrentDictionary<IPhase, IPhase> nextPhases = new();
  private IPhase? currentPhase;
  private readonly ConcurrentDictionary<IPhase, IReadOnlyList<NewDiagnostic>> queuedDiagnostics = new();
  private readonly ConcurrentDictionary<IPhase, Unit> completed = new();

  public PhaseOrderedDiagnosticsReporter(Action<NewDiagnostic> processNewDiagnostic) {
    this.processNewDiagnostic = processNewDiagnostic;
  }

  bool IsFullyCompleted(IPhase phase) => !queuedDiagnostics.TryGetValue(phase, out _);
  bool IsCompleted(IPhase phase) => completed.TryGetValue(phase, out _);

  public void PhaseStart(IPhase phase) {
    if (currentPhase != null) {
      previousPhases.TryAdd(phase, currentPhase);
      nextPhases.TryAdd(currentPhase, phase);
    }

    queuedDiagnostics.TryAdd(phase, Array.Empty<NewDiagnostic>());

    currentPhase = phase;

  }

  public void PhaseFinished(IPhase phase) {

    previousPhases.TryGetValue(phase, out var previousPhase);
    var fullyCompleted = previousPhase == null || IsFullyCompleted(previousPhase);
    completed.TryAdd(phase, Unit.Default);
    if (fullyCompleted) {
      currentPhase = phase;
      while (true) {
        if (IsCompleted(currentPhase)) {
          if (queuedDiagnostics.TryRemove(currentPhase, out var queuedDiagnosticsForPhase)) {
            foreach (var diagnostic in queuedDiagnosticsForPhase!) {
              this.processNewDiagnostic(diagnostic);
            }

            if (!nextPhases.TryGetValue(currentPhase, out currentPhase)) {
              break; // Phase is the last one
            }
          } else {
            break; // Phase was not started.
          }
        } else {
          break;
        }
      }
    }
  }

  public void NewDiagnostic(NewDiagnostic newDiagnostic) {
    IPhase? previousPhase = null;
    var diagnosticPhase = newDiagnostic.Diagnostic.Phase;
    while (diagnosticPhase != null) {
      if (previousPhases.TryGetValue(diagnosticPhase, out previousPhase)) {
        break;
      }
      diagnosticPhase = diagnosticPhase.MaybeParent;
    }

    IPhase? previousUncompletedPhase = previousPhase;
    while (previousUncompletedPhase != null && !queuedDiagnostics.TryGetValue(previousUncompletedPhase, out _)) {
      previousPhases.TryGetValue(previousUncompletedPhase, out previousUncompletedPhase);
    }

    var previousPhaseIsRunning = previousUncompletedPhase != null;
    if (previousPhaseIsRunning) {
      queuedDiagnostics.AddOrUpdate(previousPhase!,
        _ => Array.Empty<NewDiagnostic>(),
        (_, existing) => existing.Concat(new[] { newDiagnostic }));
    } else {
      this.processNewDiagnostic(newDiagnostic);
    }
  }
}