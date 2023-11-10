using System;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record NewDiagnostic(Uri Uri, DafnyDiagnostic Diagnostic) : ICompilationEvent {
}