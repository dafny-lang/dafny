using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// This notification is sent when the verification phase started.
  /// </summary>
  [Method(DafnyRequestNames.VerificationStarted, Direction.ServerToClient)]
  public class VerificationStartedParams : VerificationParams {
    public VerificationStartedParams(DocumentUri documentUri, long version) : base(documentUri, version) {
    }
  }
}
