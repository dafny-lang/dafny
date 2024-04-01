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
  private readonly ConcurrentDictionary<IPhase, IReadOnlyList<NewDiagnostic>> queuedDiagnostics = new();
  private readonly ConcurrentDictionary<IPhase, Unit> completed = new();
  private IPhase? currentPhase;

  public PhaseOrderedDiagnosticsReporter(Action<NewDiagnostic> processNewDiagnostic) {
    this.processNewDiagnostic = processNewDiagnostic;
  }

  private bool SequenceCompleted(IPhase phase) => !queuedDiagnostics.TryGetValue(phase, out _);
  private bool IsCompleted(IPhase phase) => completed.TryGetValue(phase, out _);

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
    completed.TryAdd(phase, Unit.Default);
    var fullyCompleted = previousPhase == null || SequenceCompleted(previousPhase);
    if (fullyCompleted) {
      ProcessNewCompletedSequence(phase);
    }
  }

  private void ProcessNewCompletedSequence(IPhase phase)
  {
    var completedPhase = phase;
    while (true) {
      if (IsCompleted(completedPhase)) {
        if (queuedDiagnostics.TryRemove(completedPhase, out var queuedDiagnosticsForPhase)) {
          foreach (var diagnostic in queuedDiagnosticsForPhase!) {
            processNewDiagnostic(diagnostic);
          }

          if (!nextPhases.TryGetValue(completedPhase, out completedPhase)) {
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
      processNewDiagnostic(newDiagnostic);
    }
  }
}