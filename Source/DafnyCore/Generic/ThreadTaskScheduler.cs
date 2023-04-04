using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// Each queued task runs on a newly-created thread with the required
/// stack size. The default .NET task scheduler is built on the .NET
/// ThreadPool. Its policy allows it to create thousands of threads
/// if it chooses.
/// </summary>
public class ThreadTaskScheduler : TaskScheduler {
  private readonly int stackSize;
  

  public ThreadTaskScheduler(int stackSize) {
    Contract.Requires(stackSize >= 0);

    this.stackSize = stackSize;
  }

  protected override IEnumerable<Task> GetScheduledTasks() {
    // There is never a queue of scheduled, but not running, tasks.
    // So return an empty list.
    return new List<Task>();
  }

  protected override void QueueTask(Task task) {
    Thread th = new Thread(TaskMain!, stackSize);
    th.Name = ThreadNames;
    th.Start(task);
  }

  private string ThreadNames => "stackSize" + stackSize;

  protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued) {
    if (taskWasPreviouslyQueued) {
      return false;
    }
    if (Thread.CurrentThread.Name == ThreadNames) {
      return TryExecuteTask(task);
    }
    return false;
  }

  private void TaskMain(object data) {
    Task t = (Task)data;
    TryExecuteTask(t);
  }
}