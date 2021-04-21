using MediatR;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// Base type for verification notifications.
  /// </summary>
  public class VerificationParams : IRequest, IRequest<Unit> {
    /// <summary>
    /// Gets the URI of the document whose verification completed.
    /// </summary>
#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.
    public DocumentUri Uri { get; set; }
#pragma warning restore CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public long Version { get; set; }
  }
}
