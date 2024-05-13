#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Reactive;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

interface IDiagnosticsReporter {
  void PhaseStart(IPhase phase);
  void PhaseFinished(IPhase phase);
  void NewDiagnostic(NewDiagnostic newDiagnostic);
  void ChildrenDiscovered(PhaseChildrenDiscovered phaseDiscovered);
}

/// <summary>
/// Orders phases by their start time.
/// Reports diagnostics only after all phases that come before the phase of this diagnostics, have finished.
/// </summary>
class PhaseOrderedDiagnosticsReporter : IDiagnosticsReporter {
  private ILogger logger;
  private readonly Action<NewDiagnostic> processNewDiagnostic;
  private readonly Dictionary<IPhase, IPhase> previousPhases = new();
  private readonly Dictionary<IPhase, IPhase> nextPhases = new();
  private readonly Dictionary<IPhase, IReadOnlyList<NewDiagnostic>> queuedDiagnostics = new();
  private readonly Dictionary<IPhase, Unit> completed = new();
  private IPhase? currentPhase;
  private readonly object myLock = new();

  private IPhase userPhase = new PhaseFromObject(new object(), null);

  public PhaseOrderedDiagnosticsReporter(Action<NewDiagnostic> processNewDiagnostic, ILogger logger) {
    this.processNewDiagnostic = processNewDiagnostic;
    this.logger = logger;
    previousPhases.TryAdd(RootPhase.Instance, userPhase);
  }

  private bool SequenceCompleted(IPhase phase) => !queuedDiagnostics.TryGetValue(phase, out _);
  private bool IsCompleted(IPhase phase) => completed.TryGetValue(phase, out _);

  public void PhaseStart(IPhase phase) {
    lock (myLock) {
      if (currentPhase != null) {
        previousPhases.TryAdd(phase, currentPhase);
        nextPhases.TryAdd(currentPhase, phase);
      }

      queuedDiagnostics.TryAdd(phase, Array.Empty<NewDiagnostic>());

      currentPhase = phase;
    }
  }

  public void PhaseFinished(IPhase phase) {
    lock (myLock) {
      previousPhases.TryGetValue(phase, out var previousPhase);
      completed.TryAdd(phase, Unit.Default);
      var fullyCompleted = previousPhase == null || SequenceCompleted(previousPhase);
      if (fullyCompleted) {
        ProcessNewCompletedSequence(phase);
      }
    }
  }

  private void ProcessNewCompletedSequence(IPhase phase) {
    var completedPhase = phase;
    while (true) {
      if (IsCompleted(completedPhase)) {
        if (queuedDiagnostics.Remove(completedPhase, out var queuedDiagnosticsForPhase)) {
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
    lock (myLock) {
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
          Array.Empty<NewDiagnostic>(),
          (_, existing) => existing.Concat(new[] { newDiagnostic }));
      } else {
        processNewDiagnostic(newDiagnostic);
      }
    }
  }

  public void ChildrenDiscovered(PhaseChildrenDiscovered phaseDiscovered) {
    // if (previousPhases.TryGetValue(phaseDiscovered.Phase, out var previous)) {
    //   foreach (var child in phaseDiscovered.Children) {
    //     queuedDiagnostics.TryAdd(child, Array.Empty<NewDiagnostic>());
    //     previousPhases.TryAdd(child, previous);
    //     nextPhases.TryAdd(previous, child);
    //     previous = child;
    //   }
    //   previousPhases.TryAdd(phaseDiscovered.Phase, previous);
    //   nextPhases.TryAdd(previous, phaseDiscovered.Phase);
    // } else {
    //   throw new Exception();
    // }
  }
}