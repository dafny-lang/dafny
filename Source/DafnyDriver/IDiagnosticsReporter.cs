#nullable enable
using Microsoft.Dafny;

namespace DafnyDriver.Commands;

interface IDiagnosticsReporter {
  void PhaseStart(IPhase phase);
  void PhaseFinished(IPhase phase);
  void NewDiagnostic(NewDiagnostic newDiagnostic);
}