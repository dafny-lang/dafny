using System;
using System.Collections.Generic;
using System.Linq;
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
  private IDisposable innerSubscription;
  private bool outerCompleted;
  private readonly Subject<T> result = new();

  public void OnNext(IObservable<T> next) {
    lock (this) {
      if (innerSubscription == null) {
        innerSubscription = next.Subscribe(InnerNext, InnerError, InnerCompleted);
      } else {
        allUpdates.Enqueue(next);
      }
    }
  }

  private void InnerNext(T next) {
    result.OnNext(next);
  }

  private void InnerError(Exception error) {
    result.OnError(error);
  }

  private void InnerCompleted() {
    lock (this) {
      innerSubscription = null;
      if (allUpdates.Any()) {
        var next = allUpdates.Dequeue();
        OnNext(next);
      }
    }
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
    if (outerCompleted && innerSubscription == null) {
      // ReSharper disable once InconsistentlySynchronizedField
      result.OnCompleted();
    }
  }

  public IDisposable Subscribe(IObserver<T> observer) {
    // ReSharper disable once InconsistentlySynchronizedField
    return result.Subscribe(observer);
  }
}