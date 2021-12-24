using System.Collections.Concurrent;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util {
  /// <summary>
  /// Test-class to receive and handle notifications sent by the language server.
  /// </summary>
  /// <typeparam name="TNotification">The type of the notifications sent by the language server.</typeparam>
  public class TestNotificationReceiver<TNotification> {
    private readonly SemaphoreSlim availableNotifications = new(0);
    private readonly ConcurrentQueue<TNotification> notifications = new();

    public void NotificationReceived(TNotification request) {
      notifications.Enqueue(request);
      availableNotifications.Release();
    }

    public async Task<TNotification> AwaitNextNotificationAsync(CancellationToken cancellationToken) {
      await availableNotifications.WaitAsync(cancellationToken);
      if (notifications.TryDequeue(out var notification)) {
        return notification;
      }
      throw new System.InvalidOperationException("got a signal for a received notification but it was not present in the queue");
    }
  }

  class DiagnosticsReceiver : TestNotificationReceiver<PublishDiagnosticsParams> {


    public async Task<Diagnostic[]> AwaitNextDiagnosticsAsync(CancellationToken cancellationToken) {
      var result = await AwaitNextNotificationAsync(cancellationToken);
      return result.Diagnostics.ToArray();
    }
    public async Task<Diagnostic[]> AwaitVerificationDiagnosticsAsync(CancellationToken cancellationToken) {
      await AwaitNextNotificationAsync(cancellationToken);
      var result = await AwaitNextNotificationAsync(cancellationToken);
      return result.Diagnostics.ToArray();
    }

    // This change is to ensure that no diagnostics are remaining in the report queue.
    // var verificationDocumentItem = CreateTestDocument("class X {}", "verification.dfy");
    // await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationTokenWithHighTimeout);
    // var verificationReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
    // Assert.AreEqual(verificationDocumentItem.Uri, verificationReport.Uri);
    public async Task<bool> AreMoreDiagnosticsComing(int timeout = 100) {
      var moreDiagnostics = AwaitNextNotificationAsync(CancellationToken.None);
      return await Task.WhenAny(moreDiagnostics, Task.Delay(timeout)) == moreDiagnostics;
    }
  }
}
