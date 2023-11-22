module ConcurrentExamples {

  import opened DafnyStdLibs.Concurrent
  import opened DafnyStdLibs.Wrappers
  import opened Helpers

  const p1: nat -> bool := _ => true
  const p2: (nat, nat) -> bool := (_, _) => true

  datatype Copy = A | B

  class Application {
    var mutex: Lock
    var box: AtomicBox<nat>
    var primary: MutableMap<nat, nat>
    var secondaryA: MutableMap<nat, nat>
    var secondaryB: MutableMap<nat, nat>

    constructor ()
      ensures Valid()
      ensures fresh({mutex, box, primary, secondaryA, secondaryB})
    {
      mutex := new Lock();
      box := new AtomicBox(p1, 0);
      primary := new MutableMap(p2);
      secondaryA := new MutableMap(p2);
      secondaryB := new MutableMap(p2);
    }

    ghost predicate Valid()
      reads this`box, this`primary, this`secondaryA, this`secondaryB, this.box, this.primary, this.secondaryA, this.secondaryB
    {
      box.inv == p1 && primary.inv == p2 && secondaryA.inv == p2 && secondaryB.inv == p2
      && box.Valid() && primary.Valid() && secondaryA.Valid() && secondaryB.Valid()
    }

    method Write(n: nat)
      requires Valid()
      modifies box
      ensures Valid()
    {
      box.Put(n);
    }

    method Commit(slot: nat)
      requires Valid()
      modifies primary
      ensures Valid()
    {
      var value := box.Get();
      primary.Put(slot, value);
    }

    method Propagate(slot: nat)
      requires Valid()
      modifies secondaryA, secondaryB
      ensures Valid()
    {
      mutex.Lock();
      var val := primary.Get(slot);
      if val.Some? {
        secondaryA.Put(slot, val.value);
      }
      val := primary.Get(slot);
      if val.Some? {
        secondaryB.Put(slot, val.value);
      }
      mutex.Unlock();
    }

    method Read(copy: Copy, slot: nat) returns (r: Option<nat>)
      requires Valid()
    {
      match copy
      case A => r := secondaryA.Get(slot);
      case B => r := secondaryB.Get(slot);
    }

    method EverythingElse()
      requires Valid()
      modifies primary
      ensures Valid()
    {
      assert primary.inv(0,0);
      primary.Remove(0);
      var keys := primary.Keys();
      print keys, "\n";
      var used := primary.HasKey(0);
      print used, "\n";
      var values := primary.Values();
      print values, "\n";
      var items := primary.Items();
      print items, "\n";
      primary.Put(0, 0);
      primary.Put(1, 1);
      items := primary.Items();
      print items, "\n";
      print |items|, "\n";
      var card := primary.Size();
      print card, "\n";
      var card' := primary.Size();
    }
  }

  method {:test} TestApplication() {
    var a := new Application();
    a.Write(0);
    a.Commit(0);
    a.Propagate(0);
    var r := a.Read(A, 0);
    expect(r == Some(0));
  }

  method {:test} TestKeys() {
    var mmap := new MutableMap(p2);
    var keys := mmap.Keys();
    expect(keys == {});
    mmap.Put(0, 0);
    keys := mmap.Keys();
    expect(keys == {0});
  }

  method {:test} TestHasKey() {
    var mmap := new MutableMap(p2);
    var b := mmap.HasKey(0);
    expect(!b);
    mmap.Put(0, 0);
    b := mmap.HasKey(0);
    expect(b);
  }

  method {:test} TestValues() {
    var mmap := new MutableMap(p2);
    var values := mmap.Values();
    expect(values == {});
    mmap.Put(0, 0);
    values := mmap.Values();
    expect(values == {0});
  }

  method {:test} TestItems() {
    var mmap := new MutableMap(p2);
    var items := mmap.Items();
    expect(items == {});
    mmap.Put(0, 0);
    items := mmap.Items();
    expect(items == {(0, 0)});
  }

  method {:test} TestPutGet() {
    var mmap := new MutableMap(p2);
    mmap.Put(0, 0);
    var v := mmap.Get(0);
    expect(v == Some(0));
  }

  method {:test} TestRemove() {
    var mmap := new MutableMap(p2);
    mmap.Put(0, 0);
    var b := mmap.HasKey(0);
    expect(b);
    assert mmap.inv(1,1);
    mmap.Remove(1);
    b := mmap.HasKey(0);
    expect(b);
    mmap.Remove(0);
    b := mmap.HasKey(0);
    expect(!b);
  }

  method {:test} TestCardinality() {
    var mmap := new MutableMap(p2);
    mmap.Put(0, 0);
    var v := mmap.Get(0);
    expect(v == Some(0));
  }
}