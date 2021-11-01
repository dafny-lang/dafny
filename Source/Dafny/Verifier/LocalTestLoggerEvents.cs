using System;
using System.Collections.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;
using Microsoft.VisualStudio.TestPlatform.Utilities;

namespace Microsoft.Dafny {
  public class LocalTestLoggerEvents : TestLoggerEvents {
    private JobQueue<Action> loggerEventQueue;
    private bool isDisposed;
    private bool isBoundsOnLoggerEventQueueEnabled;

    public LocalTestLoggerEvents()
    {
      this.isBoundsOnLoggerEventQueueEnabled = LocalTestLoggerEvents.IsBoundsEnabledOnLoggerEventQueue();
      this.loggerEventQueue = new JobQueue<Action>(new Action<Action>(this.ProcessQueuedJob), "Test Logger", this.GetMaxNumberOfJobsInQueue(), this.GetMaxBytesQueueCanHold(), this.isBoundsOnLoggerEventQueueEnabled, (Action<string>) (message => EqtTrace.Error(message)));
      this.loggerEventQueue.Pause();
    }

    public override event EventHandler<TestRunMessageEventArgs> TestRunMessage;

    public override event EventHandler<TestRunStartEventArgs> TestRunStart;

    public override event EventHandler<TestResultEventArgs> TestResult;

    public override event EventHandler<TestRunCompleteEventArgs> TestRunComplete;

    public override event EventHandler<DiscoveryStartEventArgs> DiscoveryStart;

    public override event EventHandler<TestRunMessageEventArgs> DiscoveryMessage;

    public override event EventHandler<DiscoveredTestsEventArgs> DiscoveredTests;

    public override event EventHandler<DiscoveryCompleteEventArgs> DiscoveryComplete;

    public void Dispose()
    {
      if (this.isDisposed)
        return;
      this.isDisposed = true;
      this.loggerEventQueue.Resume();
      this.loggerEventQueue.Dispose();
    }

    internal void EnableEvents()
    {
      this.CheckDisposed();
      this.loggerEventQueue.Resume();
      this.loggerEventQueue.Flush();
    }

    internal void RaiseTestRunMessage(TestRunMessageEventArgs args)
    {
      if (args == null)
        throw new ArgumentNullException(nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.TestRunMessage), (EventArgs) args, 0, "InternalTestLoggerEvents.SendTestRunMessage");
    }

    internal void WaitForEventCompletion() => this.loggerEventQueue.Flush();

    internal void RaiseTestResult(TestResultEventArgs args)
    {
      ValidateArg.NotNull<TestResultEventArgs>(args, nameof (args));
      this.CheckDisposed();
      int size = 0;
      if (this.isBoundsOnLoggerEventQueueEnabled)
        size = LocalTestLoggerEvents.FindTestResultSize(args) * 2;
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.TestResult), (EventArgs) args, size, "InternalTestLoggerEvents.SendTestResult");
    }

    internal void RaiseTestRunStart(TestRunStartEventArgs args)
    {
      ValidateArg.NotNull<TestRunStartEventArgs>(args, nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.TestRunStart), (EventArgs) args, 0, "InternalTestLoggerEvents.SendTestRunStart");
    }

    internal void RaiseDiscoveryStart(DiscoveryStartEventArgs args)
    {
      ValidateArg.NotNull<DiscoveryStartEventArgs>(args, nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.DiscoveryStart), (EventArgs) args, 0, "InternalTestLoggerEvents.SendDiscoveryStart");
    }

    internal void RaiseDiscoveryMessage(TestRunMessageEventArgs args)
    {
      ValidateArg.NotNull<TestRunMessageEventArgs>(args, nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.DiscoveryMessage), (EventArgs) args, 0, "InternalTestLoggerEvents.SendDiscoveryMessage");
    }

    internal void RaiseDiscoveredTests(DiscoveredTestsEventArgs args)
    {
      ValidateArg.NotNull<DiscoveredTestsEventArgs>(args, nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.DiscoveredTests), (EventArgs) args, 0, "InternalTestLoggerEvents.SendDiscoveredTests");
    }

    internal void RaiseDiscoveryComplete(DiscoveryCompleteEventArgs args)
    {
      ValidateArg.NotNull<DiscoveryCompleteEventArgs>(args, nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.DiscoveryComplete), (EventArgs) args, 0, "InternalTestLoggerEvents.SendDiscoveryComplete");
      this.loggerEventQueue.Flush();
    }

    internal void RaiseTestRunComplete(TestRunCompleteEventArgs args)
    {
      ValidateArg.NotNull<TestRunCompleteEventArgs>(args, nameof (args));
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.TestRunComplete), (EventArgs) args, 0, "InternalTestLoggerEvents.SendTestRunComplete");
      this.loggerEventQueue.Flush();
    }

    internal void CompleteTestRun(
      ITestRunStatistics stats,
      bool isCanceled,
      bool isAborted,
      Exception error,
      Collection<AttachmentSet> attachmentSet,
      TimeSpan elapsedTime)
    {
      this.CheckDisposed();
      this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.TestRunComplete), (EventArgs) new TestRunCompleteEventArgs(stats, isCanceled, isAborted, error, attachmentSet, elapsedTime), 0, "InternalTestLoggerEvents.SendTestRunComplete");
      this.loggerEventQueue.Flush();
    }

    private void TestRunMessageHandler(object sender, TestRunMessageEventArgs e) => this.SafeInvokeAsync((Func<MulticastDelegate>) (() => (MulticastDelegate) this.TestRunMessage), (EventArgs) e, 0, "InternalTestLoggerEvents.SendMessage");

    private void SafeInvokeAsync(
      Func<MulticastDelegate> eventHandlersFactory,
      EventArgs args,
      int size,
      string traceDisplayName)
    {
      ValidateArg.NotNull<Func<MulticastDelegate>>(eventHandlersFactory, nameof (eventHandlersFactory));
      ValidateArg.NotNull<EventArgs>(args, nameof (args));
      this.loggerEventQueue.QueueJob((Action) (() =>
      {
        MulticastDelegate delegates = eventHandlersFactory();
        if ((object) delegates == null)
          return;
        delegates.SafeInvoke((object) this, args, traceDisplayName);
      }), size);
    }

    private void ProcessQueuedJob(Action action) => action();

    private void CheckDisposed()
    {
      if (this.isDisposed)
        throw new ObjectDisposedException(typeof (TestLoggerEvents).FullName);
    }

    private int GetMaxNumberOfJobsInQueue() => this.GetSetting("MaxNumberOfEventsLoggerEventQueueCanHold", 500);

    private int GetMaxBytesQueueCanHold() => this.GetSetting("MaxBytesLoggerEventQueueCanHold", 25000000);

    private static bool IsBoundsEnabledOnLoggerEventQueue()
    {
      string str = (string) null;
      bool result;
      if (string.IsNullOrEmpty(str))
        result = true;
      else if (!bool.TryParse(str, out result))
        result = true;
      return result;
    }

    private static int FindTestResultSize(TestResultEventArgs args)
    {
      int num = 0;
      if (args.Result.Messages.Count != 0)
      {
        foreach (TestResultMessage message in args.Result.Messages)
        {
          if (!string.IsNullOrEmpty(message.Text))
            num += message.Text.Length;
        }
      }
      return num;
    }

    private int GetSetting(string appSettingKey, int defaultValue)
    {
      string s = (string) null;
      int result;
      if (string.IsNullOrEmpty(s))
        result = defaultValue;
      else if (!int.TryParse(s, out result) || result < 1)
      {
        EqtTrace.Warning("Unacceptable value '{0}' of {1}. Using default {2}", (object) s, (object) appSettingKey, (object) defaultValue);
        result = defaultValue;
      }
      return result;
    }
  }
}