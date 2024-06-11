using MediatR;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// DTO used to communicate the current compilation status to the LSP client.
  /// </summary>
  [Method(DafnyRequestNames.GhostDiagnostics, Direction.ServerToClient)]
  public class GhostDiagnosticsParams : IRequest, IRequest<Unit> {
    /// <summary>
    /// Gets the URI of the document whose verification completed.
    /// </summary>
    public DocumentUri Uri { get; init; }

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public int? Version { get; init; }

    /// <summary>
    /// Gets the ghost state diagnostics.
    /// </summary>
    public Container<Diagnostic> Diagnostics { get; init; }
  }
}
