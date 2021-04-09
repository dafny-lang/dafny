using OmniSharp.Extensions.JsonRpc;

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// This notification is sent when the verification phase completed.
  /// </summary>
  [Method(DafnyRequestNames.VerificationCompleted, Direction.ServerToClient)]
  public class VerificationCompletedParams : VerificationParams {
    /// <summary>
    /// <c>True</c> if the document has no verification errors.
    /// </summary>
    public bool Verified { get; set; }
  }
}
