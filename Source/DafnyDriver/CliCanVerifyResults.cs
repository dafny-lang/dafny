using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace DafnyDriver.Commands;

struct CliCanVerifyResults {
  public readonly TaskCompletionSource Finished = new();
  public readonly ConcurrentBag<(IImplementationTask, Completed)> CompletedParts = new();
  public readonly ConcurrentBag<IImplementationTask> Tasks = new();

  public CliCanVerifyResults() {
  }
}