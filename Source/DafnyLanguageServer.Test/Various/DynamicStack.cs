using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.Dafny;

[AsyncMethodBuilder(typeof(DynamicStackBuilder))]
class DynamicStack {
  public void Run() {
    DynamicStackBuilder.Builder.Value!.Run();
  }

  public DynamicStackBuilder GetAwaiter() {
    return DynamicStackBuilder.Builder.Value;
  }
}


class DynamicStackBuilder : INotifyCompletion {
  public static readonly ThreadLocal<DynamicStackBuilder> Builder = new(() => new DynamicStackBuilder());
  private static DynamicStack TheOne = new();

  public static DynamicStackBuilder Create() {
    return Builder.Value;
  }

  private readonly Stack<IAsyncStateMachine> todos = new();

  public void Run() {
    var todo = todos.Pop();
    todo.MoveNext();

    while (todos.Any()) {
      var machine = todos.Pop();
      machine.MoveNext();
    }
  }

  public void Start<TStateMachine>(ref TStateMachine stateMachine)
    where TStateMachine : IAsyncStateMachine {
    todos.Push(stateMachine);
  }

  public void SetException(Exception exception) {
    throw exception;
  }

  public void SetResult() {
  }

  public void SetStateMachine(IAsyncStateMachine stateMachine) {
  }

  public void AwaitOnCompleted<TAwaiter, TStateMachine>(
    ref TAwaiter awaiter, ref TStateMachine stateMachine)
    where TAwaiter : INotifyCompletion
    where TStateMachine : IAsyncStateMachine {
    // Place action is on top of continuation
    var action = todos.Pop();
    todos.Push(stateMachine);
    todos.Push(action);
  }

  public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(
    ref TAwaiter awaiter, ref TStateMachine stateMachine)
    where TAwaiter : ICriticalNotifyCompletion
    where TStateMachine : IAsyncStateMachine {
    // Place action is on top of continuation
    var action = todos.Pop();
    todos.Push(stateMachine);
    todos.Push(action);
  }

  public DynamicStack Task => TheOne;

  public bool IsCompleted => false;

  public void GetResult() {
  }

  public void OnCompleted(System.Action continuation) {
    throw new NotImplementedException();
  }
}

[TestClass]
public class TestExperiment {

  [TestMethod]
  public void DaTest() {
    RealThing(2).Run();
  }

  private async DynamicStack RealThing(int iterations) {
    Console.WriteLine("Before " + iterations);
    if (iterations > 0) {
      await RealThing2(iterations - 1);
    }
    Console.WriteLine("After " + iterations);
  }

  private async DynamicStack RealThing2(int iterations) {
    Console.WriteLine("Before " + iterations);
    if (iterations > 0) {
      await RealThing(iterations - 1);
    }
    Console.WriteLine("After2 " + iterations);
  }
  
  [TestMethod]
  public void BoomTest() {
    Boom(100_000);
  }
  private void Boom(int iterations) {
    if (iterations > 0) {
      Boom(iterations - 1);
    }
  }
}