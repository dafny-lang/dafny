
using System;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record InternalCompilationException(Exception Exception) : ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {
    var internalErrorDiagnostic = new Diagnostic {
      Message =
        "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
        Exception,
      Severity = DiagnosticSeverity.Error,
      Range = new Range(0, 0, 0, 1)
    };
    return previousState with {
      Status = CompilationStatus.InternalException,
      StaticDiagnostics = ImmutableDictionary<Uri, ImmutableList<Diagnostic>>.Empty.Add(previousState.Input.Uri.ToUri(), ImmutableList.Create(internalErrorDiagnostic))
    };
  }
}