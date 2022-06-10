using MediatR;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// Obsolete, replaced by FileVerificationStatus
  ///
  /// Describes the current compilation status. Useful for a status bar.
  /// </summary>
  [Method(DafnyRequestNames.CompilationStatus, Direction.ServerToClient)]
  public class CompilationStatusParams : IRequest {
    /// <summary>
    /// Gets the URI of the document whose verification completed.
    /// </summary>
#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.
    public DocumentUri Uri { get; init; }
#pragma warning restore CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public int? Version { get; init; }

    /// <summary>
    /// Gets the status of the compilation.
    /// </summary>
    public CompilationStatus Status { get; init; }

    /// <summary>
    /// Gets additional information about the current status
    /// </summary>
    public string? Message { get; init; }
  }
}
