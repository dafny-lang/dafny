using System.Collections.Concurrent;
using System.Collections.Generic;
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
    private readonly List<TNotification> notificationHistory = new();

    public void NotificationReceived(TNotification request) {
      notifications.Enqueue(request);
      availableNotifications.Release();
    }

    public bool HasPendingNotifications => !notifications.IsEmpty;

    public IReadOnlyList<TNotification> History => notificationHistory;

    public void ClearHistory() {
      notificationHistory.Clear();
    }

    public async Task<TNotification> AwaitNextNotificationAsync(CancellationToken cancellationToken) {
      await availableNotifications.WaitAsync(cancellationToken);
      if (notifications.TryDequeue(out var notification)) {
        notificationHistory.Add(notification);
        return notification;
      }
      throw new System.InvalidOperationException("got a signal for a received notification but it was not present in the queue");
    }
  }
}
