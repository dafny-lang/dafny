using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util {

  /// <summary>
  /// Test-class to receive and handle notifications sent by the language server.
  /// </summary>
  /// <typeparam name="TNotification">The type of the notifications sent by the language server.</typeparam>
  public class TestNotificationReceiver<TNotification> {

    private SemaphoreSlim availableNotifications = new(0);
    private readonly ConcurrentQueue<TNotification> notifications = new();
    private readonly List<TNotification> notificationHistory = new();
    private readonly ILogger logger;

    public TestNotificationReceiver(ILogger logger) {
      this.logger = logger;
    }

    public void NotificationReceived(TNotification request) {
      logger.LogTrace($"Received {request.Stringify()}");
      notifications.Enqueue(request);
      notificationHistory.Add(request);
      availableNotifications.Release();
    }

    public bool HasPendingNotifications => !notifications.IsEmpty;

    public IReadOnlyList<TNotification> History => notificationHistory;

    public void ClearHistory() {
      notificationHistory.Clear();
    }

    public TNotification GetLast(Func<TNotification, bool> predicate) {
      var result = History.LastOrDefault(predicate);
      ClearQueue();
      return result;
    }

    public void ClearQueue() {
      notifications.Clear();
      availableNotifications = new(0);
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
