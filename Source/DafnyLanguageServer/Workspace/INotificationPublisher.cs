namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the diagnostics
  /// of a <see cref="Compilation"/> to the LSP client.
  /// </summary>
  public interface INotificationPublisher {
    /// <summary>
    /// Publishes the diagnostics of the specified dafny document to the connected LSP client.
    /// </summary>
    /// <param name="state">The document whose diagnostics should be published.</param>
    void PublishNotifications(IdeState previousState, IdeState state);

    /// <summary>
    /// Publishes the more precise real-time verification diagnostics to the connected LSP client
    /// </summary>
    void PublishGutterIcons(IdeState state, bool verificationStarted);
  }
}
