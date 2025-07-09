using System;
using System.Collections.Generic;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test;

public class MergeOrderedTest {

  /// <summary>
  /// Stream of observables: +------1------2-----3-------------------------------|
  ///   Observable-1         :      +--A-----------------B--|
  ///   Observable-2         :             +---C---------------------D--|
  ///   Observable-3         :                   +--E----------------------F--|
  ///   Merge                : +-------A-------C----E----B-----------D-----F--|
  ///   MergeOrdered         : +-------A-----------------B--C--------D--E--F-----|
  /// </summary>
  [Fact]
  public void ThreeInnerObservables() {
    var outer = new Subject<IObservable<int>>();
    var list = new List<int>();
    var merged = new MergeOrdered<int>();
    merged.Subscribe(value => list.Add(value), _ => { }, () => list.Add(-1));
    outer.Subscribe(merged);

    var first = new ReplaySubject<int>();
    var second = new ReplaySubject<int>();
    var third = new ReplaySubject<int>();

    outer.OnNext(first);

    first.OnNext(1);
    outer.OnNext(second);
    second.OnNext(3);
    outer.OnNext(third);
    third.OnNext(5);
    first.OnNext(2);
    first.OnCompleted();
    second.OnNext(4);
    second.OnCompleted();
    third.OnNext(6);
    third.OnCompleted();
    outer.OnCompleted();

    Assert.Equal([1, 2, 3, 4, 5, 6, -1], list);
  }

  [Fact]
  public void OuterCompletedFirst() {
    var outer = new Subject<IObservable<int>>();
    var list = new List<int>();
    var merged = new MergeOrdered<int>();
    merged.Subscribe(value => list.Add(value), _ => { }, () => list.Add(-1));
    outer.Subscribe(merged);

    var first = new ReplaySubject<int>();

    outer.OnNext(first);
    outer.OnCompleted();
    first.OnNext(1);
    first.OnCompleted();

    Assert.Equal([1, -1], list);
  }

  [Fact]
  public void EmptyObservable() {
    var list = new List<int>();

    var first = new ReplaySubject<int>();
    first.OnNext(1);
    first.OnCompleted();

    var merged = new MergeOrdered<int>();
    merged.Subscribe(value => list.Add(value), _ => { }, () => list.Add(-1));

    merged.OnNext(Observable.Empty<int>());
    merged.OnNext(first);
    merged.OnCompleted();

    Assert.Equal([1, -1], list);
  }

  [Fact]
  public void ComplicatedCase() {
    var list = new List<int>();

    var first = new ReplaySubject<int>();

    var merged = new MergeOrdered<int>();
    merged.Subscribe(value => list.Add(value), _ => { }, () => list.Add(-1));

    merged.OnNext(first);
    merged.OnNext(Observable.Empty<int>());
    merged.OnNext(Observable.Empty<int>());
    merged.OnCompleted();
    first.OnNext(1);
    first.OnCompleted();

    Assert.Equal([1, -1], list);
  }
}