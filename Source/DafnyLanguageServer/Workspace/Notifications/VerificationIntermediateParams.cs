using MediatR;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// DTO used to communicate the current compilation status to the LSP client.
  /// </summary>
  [Method(DafnyRequestNames.VerificationIntermediate, Direction.ServerToClient)]
  public class VerificationIntermediateParams : IRequest {
    /// <summary>
    /// Gets the URI of the document whose verification completed.
    /// </summary>
    public DocumentUri Uri { get; init; }

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public int? Version { get; init; }

    /// <summary>
    /// Gets the name of the method being verified
    /// </summary>
    public string? MethodNameBeingVerified { get; init; }

    /// <summary>
    /// Gets the name of the method that was last verified
    /// </summary>
    public string? MethodNameVerified { get; init; }

    /// <summary>
    /// Gets the verification status of the last method name that was verified
    /// </summary>
    public bool Verified { get; init; }

    /// <summary>
    /// Gets the ranges of top level members that were not verified
    /// </summary>
    public Range? Range { get; init; }
  }
}
