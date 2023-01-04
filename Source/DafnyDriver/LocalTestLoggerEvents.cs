using System;
using System.Collections.ObjectModel;
using System.Diagnostics;
using Microsoft.VisualStudio.TestPlatform.Common;
using Microsoft.VisualStudio.TestPlatform.ObjectModel;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Client;
using Microsoft.VisualStudio.TestPlatform.ObjectModel.Logging;
using Microsoft.VisualStudio.TestPlatform.Utilities;

namespace Microsoft.Dafny {

  /// <summary>
  /// Simple implementation of TestLoggerEvents in order to drive test results loggers.
  /// Copied and modified (to remove the parent TestSessionMessageLogger reference)
  /// from the internal but MIT-licensed version from inside VSTest:
  /// https://github.com/microsoft/vstest/blob/main/src/Microsoft.TestPlatform.Common/Logging/InternalTestLoggerEvents.cs
  ///
  /// Since this class is copied and modified from existing source, I haven't made any effort
  /// to align coding styles or clean up anything, for the sake of simplicity. 
  /// </summary>
  public class LocalTestLoggerEvents : TestLoggerEvents, IDisposable {
    #region Fields

    /// <summary>
    /// Queue used for events which are to be sent to the loggers.
    /// </summary>
    /// <remarks>
    /// Using the queue accomplishes two things.
    /// 1. Loggers do not need to be written to be thread safe because
    ///    we will only be raising one event to them at a time.
    /// 2. Allows all events to go to all loggers even during initialization
    ///    because we queue up all events sent until raising of events to the
    ///    loggers is enabled
    /// </remarks>
    private JobQueue<Action> loggerEventQueue;

    /// <summary>
    /// Keeps track if we are disposed.
    /// </summary>
    private bool isDisposed = false;

    /// <summary>
    /// Specifies whether logger event queue is bounded or not
    /// </summary>
    private bool isBoundsOnLoggerEventQueueEnabled;

    #endregion

    #region Constructor

    /// <summary>
    /// Default constructor.
    /// </summary>
    public LocalTestLoggerEvents() {

      // Initialize the queue and pause it.
      // Note: The queue will be resumed when events are enabled.  This is done so all
      //       loggers receive all messages.
      this.isBoundsOnLoggerEventQueueEnabled = IsBoundsEnabledOnLoggerEventQueue();
      this.loggerEventQueue = new JobQueue<Action>(
        this.ProcessQueuedJob,
        "Test Logger",
        GetMaxNumberOfJobsInQueue(),
        GetMaxBytesQueueCanHold(),
        this.isBoundsOnLoggerEventQueueEnabled,
        (message) => EqtTrace.Error(message));
      this.loggerEventQueue.Pause();
    }

    #endregion

    #region Events

    /// <summary>
    /// Raised when a test message is received.
    /// </summary>
    public override event EventHandler<TestRunMessageEventArgs> TestRunMessage;

    /// <summary>
    /// Raised when a test run starts.
    /// </summary>
    public override event EventHandler<TestRunStartEventArgs> TestRunStart;

    /// <summary>
    /// Raised when a test result is received.
    /// </summary>
    public override event EventHandler<TestResultEventArgs> TestResult;

    /// <summary>
    /// Raised when a test run is complete.
    /// </summary>
    public override event EventHandler<TestRunCompleteEventArgs> TestRunComplete;

    /// <summary>
    /// Raised when test discovery starts.
    /// </summary>
    public override event EventHandler<DiscoveryStartEventArgs> DiscoveryStart;

    /// <summary>
    /// Raised when a discovery message is received.
    /// </summary>
    public override event EventHandler<TestRunMessageEventArgs> DiscoveryMessage;

    /// <summary>
    /// Raised when discovered tests are received
    /// </summary>
    public override event EventHandler<DiscoveredTestsEventArgs> DiscoveredTests;

    /// <summary>
    /// Raised when test discovery is complete
    /// </summary>
    public override event EventHandler<DiscoveryCompleteEventArgs> DiscoveryComplete;

    #endregion

    #region IDisposable

    /// <summary>
    /// Waits for all pending messages to be processed by the loggers cleans up.
    /// </summary>
    public void Dispose() {
      if (this.isDisposed) {
        return;
      }

      this.isDisposed = true;

      // Ensure that the queue is processed before returning.
      this.loggerEventQueue.Resume();
      this.loggerEventQueue.Dispose();
    }

    #endregion

    #region Internal Methods

    /// <summary>
    /// Enables sending of events to the loggers which are registered and flushes the queue.
    /// </summary>
    /// <remarks>
    /// By default events are disabled and will not be raised until this method is called.
    /// This is done because during logger initialization, errors could be sent and we do not
    /// want them broadcast out to the loggers until all loggers have been enabled.  Without this
    /// all loggers would not receive the errors which were sent prior to initialization finishing.
    /// </remarks>
    internal void EnableEvents() {
      this.CheckDisposed();

      this.loggerEventQueue.Resume();

      // Allow currently queued events to flush from the queue.  This is done so that information
      // logged during initialization completes processing before we begin other tasks.  This is
      // important for instance when errors are logged during initialization and need to be output
      // to the console before we begin outputting other information to the console.
      this.loggerEventQueue.Flush();
    }

    /// <summary>
    /// Raises a test run message event to the enabled loggers.
    /// </summary>
    /// <param name="args">Arguments to be raised.</param>
    internal void RaiseTestRunMessage(TestRunMessageEventArgs args) {
      if (args == null) {
        throw new ArgumentNullException(nameof(args));
      }

      this.CheckDisposed();

      // Sending 0 size as this event is not expected to contain any data.
      this.SafeInvoke(() => this.TestRunMessage, args, 0, "InternalTestLoggerEvents.SendTestRunMessage");
    }

    internal void WaitForEventCompletion() {
      this.loggerEventQueue.Flush();
    }

    /// <summary>
    /// Raises a test result event to the enabled loggers.
    /// </summary>
    /// <param name="args">Arguments to to be raised.</param>
    internal void RaiseTestResult(TestResultEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      this.CheckDisposed();

      // find the approx size of test result
      int resultSize = 0;
      if (this.isBoundsOnLoggerEventQueueEnabled) {
        resultSize = FindTestResultSize(args) * sizeof(char);
      }

      this.SafeInvoke(() => this.TestResult, args, resultSize, "InternalTestLoggerEvents.SendTestResult");
    }

    /// <summary>
    /// Raises the test run start event to enabled loggers.
    /// </summary>
    /// <param name="args">Arguments to be raised.</param>
    internal void RaiseTestRunStart(TestRunStartEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      CheckDisposed();

      this.SafeInvoke(() => this.TestRunStart, args, 0, "InternalTestLoggerEvents.SendTestRunStart");
    }

    /// <summary>
    /// Raises a discovery start event to the enabled loggers.
    /// </summary>
    /// <param name="args">Arguments to be raised.</param>
    internal void RaiseDiscoveryStart(DiscoveryStartEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      CheckDisposed();

      SafeInvoke(() => this.DiscoveryStart, args, 0, "InternalTestLoggerEvents.SendDiscoveryStart");
    }

    /// <summary>
    /// Raises a discovery message event to the enabled loggers.
    /// </summary>
    /// <param name="args">Arguments to be raised.</param>
    internal void RaiseDiscoveryMessage(TestRunMessageEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      this.CheckDisposed();

      // Sending 0 size as this event is not expected to contain any data.
      this.SafeInvoke(() => this.DiscoveryMessage, args, 0, "InternalTestLoggerEvents.SendDiscoveryMessage");
    }

    /// <summary>
    /// Raises discovered tests event to the enabled loggers.
    /// </summary>
    /// <param name="args"> Arguments to be raised. </param>
    internal void RaiseDiscoveredTests(DiscoveredTestsEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      CheckDisposed();

      SafeInvoke(() => this.DiscoveredTests, args, 0, "InternalTestLoggerEvents.SendDiscoveredTests");
    }

    /// <summary>
    /// Raises discovery complete event to the enabled loggers.
    /// </summary>
    /// <param name="args"> Arguments to be raised. </param>
    internal void RaiseDiscoveryComplete(DiscoveryCompleteEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      CheckDisposed();

      // Sending 0 size as this event is not expected to contain any data.
      SafeInvoke(() => this.DiscoveryComplete, args, 0, "InternalTestLoggerEvents.SendDiscoveryComplete");

      // Wait for the loggers to finish processing the messages for the run.
      this.loggerEventQueue.Flush();
    }

    /// <summary>
    /// Raises test run complete to the enabled loggers
    /// </summary>
    /// <param name="args"> Arguments to be raised </param>
    internal void RaiseTestRunComplete(TestRunCompleteEventArgs args) {
      ValidateArg.NotNull(args, nameof(args));

      CheckDisposed();

      // Size is being send as 0. (It is good to send the size as the job queue uses it)
      SafeInvoke(() => this.TestRunComplete, args, 0, "InternalTestLoggerEvents.SendTestRunComplete");

      // Wait for the loggers to finish processing the messages for the run.
      this.loggerEventQueue.Flush();
    }

    /// <summary>
    /// Raise the test run complete event to test loggers and waits
    /// for the events to be processed.
    /// </summary>
    /// <param name="stats">Specifies the stats of the test run.</param>
    /// <param name="isCanceled">Specifies whether the test run is canceled.</param>
    /// <param name="isAborted">Specifies whether the test run is aborted.</param>
    /// <param name="error">Specifies the error that occurs during the test run.</param>
    /// <param name="attachmentSet">Run level attachment sets</param>
    /// <param name="elapsedTime">Time elapsed in just running the tests.</param>
    internal void CompleteTestRun(ITestRunStatistics stats, bool isCanceled, bool isAborted, Exception error,
      Collection<AttachmentSet> attachmentSet, TimeSpan elapsedTime) {
      this.CheckDisposed();

      var args = new TestRunCompleteEventArgs(stats, isCanceled, isAborted, error, attachmentSet, elapsedTime);

      // Sending 0 size as this event is not expected to contain any data.
      this.SafeInvoke(() => this.TestRunComplete, args, 0, "InternalTestLoggerEvents.SendTestRunComplete");

      // Wait for the loggers to finish processing the messages for the run.
      this.loggerEventQueue.Flush();
    }

    #endregion

    #region Private Members

    /// <summary>
    /// Called when a test run message is sent through the ITestRunMessageLogger which is exported.
    /// </summary>
    private void TestRunMessageHandler(object sender, TestRunMessageEventArgs e) {
      // Broadcast the message to the loggers.
      this.SafeInvoke(() => this.TestRunMessage, e, 0, "InternalTestLoggerEvents.SendMessage");
    }

    /// <summary>
    /// Invokes each of the subscribers of the event and handles exceptions which are thrown
    /// ensuring that each handler is invoked even if one throws.
    /// The actual calling of the subscribers is done on a background thread.
    /// </summary>
    private void SafeInvoke(Func<MulticastDelegate> eventHandlersFactory, EventArgs args, int size,
      string traceDisplayName) {
      ValidateArg.NotNull(eventHandlersFactory, nameof(eventHandlersFactory));
      ValidateArg.NotNull(args, nameof(args));

      // Invoke the handlers on a background thread.
      this.loggerEventQueue.QueueJob(
        () => {
          var eventHandlers = eventHandlersFactory();
          eventHandlers?.SafeInvoke(this, args, traceDisplayName);
        }, size);
    }

    /// <summary>
    /// Method called to process a job which is coming from the logger event queue.
    /// </summary>
    private void ProcessQueuedJob(Action action) {
      action();
    }

    /// <summary>
    /// Throws if we are disposed.
    /// </summary>
    private void CheckDisposed() {
      if (this.isDisposed) {
        throw new ObjectDisposedException(typeof(TestLoggerEvents).FullName);
      }
    }

    /// <summary>
    /// The method parses the config file of vstest.console.exe to see if the Max Job Queue Length is defined.
    /// Return the Max Queue Length so defined or a default value specified by TestPlatformDefaults.DefaultMaxLoggerEventsToCache
    /// </summary>
    private int GetMaxNumberOfJobsInQueue() {
      return GetSetting(TestPlatformDefaults.MaxNumberOfEventsLoggerEventQueueCanHold,
        TestPlatformDefaults.DefaultMaxNumberOfEventsLoggerEventQueueCanHold);
    }

    /// <summary>
    /// The method parses the config file of vstest.console.exe to see if the Max Job Queue size is defined.
    /// Return the Max Queue size so defined or a default value specified by TestPlatformDefaults.DefaultMaxJobQueueSize
    /// </summary>
    private int GetMaxBytesQueueCanHold() {
      return GetSetting(TestPlatformDefaults.MaxBytesLoggerEventQueueCanHold,
        TestPlatformDefaults.DefaultMaxBytesLoggerEventQueueCanHold);
    }

    /// <summary>
    /// Returns whether flow control on logger events queue should be enabled or not. Default is enabled.
    /// </summary>
    private static bool IsBoundsEnabledOnLoggerEventQueue() {
      bool enableBounds;
#if NETFRAMEWORK
            string enableBoundsOnEventQueueIsDefined =
 ConfigurationManager.AppSettings[TestPlatformDefaults.EnableBoundsOnLoggerEventQueue];
#else
      string enableBoundsOnEventQueueIsDefined = null;
#endif
      if (string.IsNullOrEmpty(enableBoundsOnEventQueueIsDefined)) {
        enableBounds = TestPlatformDefaults.DefaultEnableBoundsOnLoggerEventQueue;
      } else {
        if (!(bool.TryParse(enableBoundsOnEventQueueIsDefined, out enableBounds))) {
          enableBounds = TestPlatformDefaults.DefaultEnableBoundsOnLoggerEventQueue;
        }
      }

      return enableBounds;
    }

    /// <summary>
    /// Returns the approximate size of a TestResult instance.
    /// </summary>
    private static int FindTestResultSize(TestResultEventArgs args) {
      Debug.Assert(args != null && args.Result != null);

      int size = 0;

      if (args.Result.Messages.Count != 0) {
        foreach (TestResultMessage msg in args.Result.Messages) {
          if (!string.IsNullOrEmpty(msg.Text)) {
            size += msg.Text.Length;
          }
        }
      }

      return size;
    }

    /// <summary>
    /// Get the appsetting value for the parameter appSettingKey. Use the parameter defaultValue if
    /// value is not there or is invalid.
    /// </summary>
    private int GetSetting(string appSettingKey, int defaultValue) {
      int value;
#if NETFRAMEWORK
            string appSettingValue = ConfigurationManager.AppSettings[appSettingKey];
#else
      string appSettingValue = null;
#endif
      if (string.IsNullOrEmpty(appSettingValue)) {
        value = defaultValue;
      } else if (!int.TryParse(appSettingValue, out value) || value < 1) {
        EqtTrace.Warning("Unacceptable value '{0}' of {1}. Using default {2}", appSettingValue, appSettingKey,
          defaultValue);
        value = defaultValue;
      }

      return value;
    }
    #endregion
  }
}