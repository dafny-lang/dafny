using System.Collections.Generic;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace DafnyDriver.Commands;

struct CliCanVerifyResults {
  public readonly TaskCompletionSource Finished = new();
  public readonly List<(IImplementationTask, Completed)> CompletedParts = new();
  public readonly HashSet<IImplementationTask> Tasks = new();

  public CliCanVerifyResults() {
  }
}