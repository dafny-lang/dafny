using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace DafnyDriver.Commands;

struct CliCanVerifyResults {
  public readonly TaskCompletionSource Finished = new();
  public readonly ConcurrentBag<(IVerificationTask Task, Completed Result)> CompletedParts = new();
  public readonly ConcurrentBag<IVerificationTask> Tasks = new();

  public CliCanVerifyResults() {
  }
}