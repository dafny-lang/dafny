using System.Collections.Concurrent;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util {
  /// <summary>
  /// Test-class to receive and handle notifications sent by the language server.
  /// </summary>
  /// <typeparam name="TNotification">The type of the notifications sent by the language server.</typeparam>
  public class TestNotificationReceiver<TNotification> {
    private readonly SemaphoreSlim availableNotifications = new(0);
    private readonly ConcurrentQueue<TNotification> notifications = new();
    private TNotification lastNotification;

    public void NotificationReceived(TNotification request) {
      lastNotification = request;
      notifications.Enqueue(request);
      availableNotifications.Release();
    }

    public async Task<TNotification> GetLastNotification(CancellationToken cancellationToken) {
      if (lastNotification != null) {
        return lastNotification;
      }

      await AwaitNextNotificationAsync(cancellationToken);
      return lastNotification;
    }


    public async Task<TNotification> AwaitNextNotificationAsync(CancellationToken cancellationToken) {
      await availableNotifications.WaitAsync(cancellationToken);
      if (notifications.TryDequeue(out var notification)) {
        return notification;
      }
      throw new System.InvalidOperationException("got a signal for a received notification but it was not present in the queue");
    }
  }
}
