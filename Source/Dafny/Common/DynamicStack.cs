using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;

namespace Microsoft.Dafny;

[AsyncMethodBuilder(typeof(DynamicStackBuilder))]
public class DynamicStack {
  public void Run() {
    DynamicStackBuilder.Builder.Value!.Run();
  }

  public DynamicStackBuilder GetAwaiter() {
    return DynamicStackBuilder.Builder.Value;
  }
}

public class DynamicStackBuilder : INotifyCompletion {
  public static readonly ThreadLocal<DynamicStackBuilder> Builder = new(() => new DynamicStackBuilder());
  private static readonly DynamicStack TheOne = new();

  public static DynamicStackBuilder Create() {
    return Builder.Value;
  }

  private readonly Stack<IAsyncStateMachine> todos = new();

  public void Run() {
    while (todos.Any()) {
      var machine = todos.Pop();
      machine.MoveNext();
    }
  }

  public void Start<TStateMachine>(ref TStateMachine stateMachine)
    where TStateMachine : IAsyncStateMachine {
    // Push recursive call
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
    // Place recursive call on top of continuation
    var recursiveCall = todos.Pop();
    todos.Push(stateMachine);
    todos.Push(recursiveCall);
  }

  public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(
    ref TAwaiter awaiter, ref TStateMachine stateMachine)
    where TAwaiter : ICriticalNotifyCompletion
    where TStateMachine : IAsyncStateMachine {
    // Place recursive call on top of continuation
    var recursiveCall = todos.Pop();
    todos.Push(stateMachine);
    todos.Push(recursiveCall);
  }

  public DynamicStack Task => TheOne;

  public bool IsCompleted => false;

  public void GetResult() {
  }

  public void OnCompleted(System.Action continuation) {
    throw new NotImplementedException();
  }
}