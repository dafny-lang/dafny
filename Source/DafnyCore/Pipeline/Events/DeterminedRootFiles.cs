using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public record FileDiagnostic(Uri Uri, Diagnostic Diagnostic);

public record DeterminedRootFiles(DafnyProject Project, IReadOnlyList<DafnyFile> Roots) : ICompilationEvent {
}