using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

public class OneOffCustomStackSizePoolTaskScheduler : TaskScheduler
{
  private readonly int stackSize;

  public static OneOffCustomStackSizePoolTaskScheduler Create(int stackSize) => new(stackSize);

  private OneOffCustomStackSizePoolTaskScheduler(int stackSize)
  {
    this.stackSize = stackSize;
  }

  protected override void QueueTask(Task task) {
    var thread = new Thread(() => TryExecuteTask(task), stackSize);
    thread.IsBackground = true;
    thread.Name = $"OneOffCustomStackSizePoolTaskScheduler thread";
    thread.Start();
  }

  protected override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued) => false;

  protected override IEnumerable<Task> GetScheduledTasks() => Enumerable.Empty<Task>();
}