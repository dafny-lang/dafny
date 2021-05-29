using OmniSharp.Extensions.JsonRpc;

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// This notification is sent when the verification phase started.
  /// </summary>
  [Method(DafnyRequestNames.VerificationStarted, Direction.ServerToClient)]
  public class VerificationStartedParams : VerificationParams {
  }
}
