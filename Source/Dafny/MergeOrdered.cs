using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive;
using System.Reactive.Linq;
using System.Reactive.Subjects;

namespace Microsoft.Dafny;


/// <summary>
/// Stream of observables: +------1------2-----3-------------------------------|
///   Observable-1         :      +--A-----------------B--|
///   Observable-2         :             +---C---------------------D--|
///   Observable-3         :                   +--E----------------------F--|
///   Merge                : +-------A-------C----E----B-----------D-----F--|
///   MergeOrdered         : +-------A-----------------B--C--------D--E--F-----|
/// </summary>
public class MergeOrdered<T> : IObservable<T>, IObserver<IObservable<T>> {
  private readonly Queue<IObservable<T>> allUpdates = new();
  private bool idle = true;
  private bool outerCompleted;
  private readonly Subject<T> result = new();
  private readonly ReplaySubject<bool> idleStates = new(1);

  public IObservable<bool> IdleChangesIncludingLast => idleStates.DistinctUntilChanged();

  public void OnNext(IObservable<T> next) {
    lock (this) {
      if (idle) {
        idle = false;
        next.Subscribe(InnerNext, InnerError, InnerCompleted);
      } else {
        allUpdates.Enqueue(next);
      }
    }
    idleStates.OnNext(idle);
  }

  private void InnerNext(T next) {
    result.OnNext(next);
  }

  private void InnerError(Exception error) {
    result.OnError(error);
  }

  private void InnerCompleted() {
    lock (this) {
      idle = true;
      if (allUpdates.Any()) {
        var next = allUpdates.Dequeue();
        OnNext(next);
      }
    }
    idleStates.OnNext(idle);
    CheckCompleted();
  }

  public void OnError(Exception error) {
    // ReSharper disable once InconsistentlySynchronizedField
    result.OnError(error);
  }

  public void OnCompleted() {
    outerCompleted = true;
    CheckCompleted();
  }

  private void CheckCompleted() {
    if (outerCompleted && idle) {
      // ReSharper disable once InconsistentlySynchronizedField
      result.OnCompleted();
      idleStates.OnCompleted();
    }
  }

  public IDisposable Subscribe(IObserver<T> observer) {
    // ReSharper disable once InconsistentlySynchronizedField
    return result.Subscribe(observer);
  }
}