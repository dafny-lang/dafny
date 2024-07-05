using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace DafnyDriver.Commands;

public record CliCanVerifyState {
  public Func<IVerificationTask, bool> TaskFilter = _ => true;
  public readonly TaskCompletionSource Finished = new();
  public readonly ConcurrentQueue<(IVerificationTask Task, Completed Result)> CompletedParts = new();
  public readonly ConcurrentBag<IVerificationTask> Tasks = new();
}