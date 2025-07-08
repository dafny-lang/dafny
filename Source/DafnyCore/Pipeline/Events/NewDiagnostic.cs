using System;

namespace Microsoft.Dafny;

public record NewDiagnostic(Uri Uri, DafnyDiagnostic Diagnostic) : ICompilationEvent {
}