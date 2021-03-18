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
    public DocumentUri Uri { get; }

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public long Version { get; }


    public VerificationParams(DocumentUri documentUri, long version) {
      Uri = documentUri;
      Version = version;
    }
  }
}
