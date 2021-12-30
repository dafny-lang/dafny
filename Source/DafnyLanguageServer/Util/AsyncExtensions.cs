using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Util;

public static class AsyncExtensions {
  /// <summary>
  /// Returns the result of the first task that completes successfully.
  /// If multiple tasks are already completed, the first one is returned.
  /// </summary>
  public static Task<T> FirstSuccessfulAsync<T>(params Task<T>[] tasks) {
    var taskList = tasks.ToList();
    var tcs = new TaskCompletionSource<T>();
    int remainingTasks = taskList.Count;
    foreach (var task in taskList) {
      if (task.IsCompletedSuccessfully) {
        tcs.SetResult(task.Result);
        break;
      }

      _ = task.ContinueWith(t => {
        if (task.IsCompletedSuccessfully) {
          tcs.TrySetResult(t.Result);
        } else if (Interlocked.Decrement(ref remainingTasks) == 0) {
          if (tasks.Any(otherTask => otherTask.IsCanceled)) {
            tcs.SetCanceled();
          } else {
            tcs.SetException(new AggregateException(tasks.SelectMany(t1 => t1.Exception!.InnerExceptions)));
          }
        }
      }, TaskScheduler.Default);
    }
    return tcs.Task;
  }
}