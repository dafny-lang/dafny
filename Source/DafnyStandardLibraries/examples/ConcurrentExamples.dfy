module ConcurrentExamples {

  import opened Std.Concurrent
  import opened Std.Wrappers
  import opened Helpers

  const p1: nat -> bool := _ => true
  const p2: (nat, nat) -> bool := (_, _) => true
  const p3: (char, nat) -> bool := (_, _) => true
  const p4: (Copy, nat) -> bool := (_, _) => true
  // const p5: (object?, nat) -> bool := (_, _) => true
  const p6: (string, nat) -> bool := (_, _) => true


  datatype Copy = A | B

  class Application {
    const mutex: Lock
    const box: AtomicBox<nat>
    const primary: MutableMap<nat, nat>
    const secondaryA: MutableMap<nat, nat>
    const secondaryB: MutableMap<nat, nat>

    constructor ()
      ensures ValidLockState()
      ensures fresh({mutex, box, primary, secondaryA, secondaryB})
    {
      mutex := new Lock();
      box := new AtomicBox(p1, 0);
      primary := new MutableMap(p2);
      secondaryA := new MutableMap(p2);
      secondaryB := new MutableMap(p2);
    }

    ghost predicate Valid()
    {
      box.inv == p1 && primary.inv == p2 && secondaryA.inv == p2 && secondaryB.inv == p2
    }

    ghost predicate ValidLockState()
      reads this.mutex
    {
      Valid() && !mutex.isLocked
    }

    @Concurrent
    method Write(n: nat)
      reads {}
      requires Valid()
    {
      box.Put(n);
    }

    @Concurrent
    method Commit(slot: nat)
      reads {}
      requires Valid()
      ensures Valid()
    {
      var value := box.Get();
      primary.Put(slot, value);
    }

    @Concurrent
    method Propagate(slot: nat)
      reads {:assume_concurrent} mutex
      requires ValidLockState()
      modifies {:assume_concurrent} mutex
      ensures ValidLockState()
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

    @Concurrent
    method Read(copy: Copy, slot: nat) returns (r: Option<nat>)
      reads {}
    {
      match copy
      case A => r := secondaryA.Get(slot);
      case B => r := secondaryB.Get(slot);
    }
  }

  @Test
  method TestApplication() {
    var a := new Application();
    a.Write(0);
    a.Commit(0);
    a.Propagate(0);
    var r := a.Read(A, 0);
    expect(r == Some(0));
  }

  @Test
  method TestKeys() {
    var mmap := new MutableMap(p2);
    var keys := mmap.Keys();
    expect(keys == {});
    mmap.Put(0, 0);
    keys := mmap.Keys();
    expect(keys == {0});
  }

  @Test
  method TestHasKey() {
    var mmap := new MutableMap(p2);
    var b := mmap.HasKey(0);
    expect(!b);
    mmap.Put(0, 0);
    b := mmap.HasKey(0);
    expect(b);
  }

  @Test
  method TestValues() {
    var mmap := new MutableMap(p2);
    var values := mmap.Values();
    expect(values == {});
    mmap.Put(0, 0);
    values := mmap.Values();
    expect(values == {0});
  }

  @Test
  method TestItems() {
    var mmap := new MutableMap(p2);
    var items := mmap.Items();
    expect(items == {});
    mmap.Put(0, 0);
    items := mmap.Items();
    expect(items == {(0, 0)});
  }

  @Test
  method TestPutGet() {
    var mmap := new MutableMap(p2);
    mmap.Put(0, 0);
    var v := mmap.Get(0);
    expect(v == Some(0));
  }

  @Test
  method TestRemove() {
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

  @Test
  method TestSize() {
    var mmap := new MutableMap(p2);
    var size := mmap.Size();
    expect(size == 0);
    mmap.Put(0, 0);
    size := mmap.Size();
    expect(size == 1);
  }

  @Test
  method TestChar() {
    var mmap := new MutableMap(p3);
    var b := mmap.HasKey('A');
    expect(!b);
    mmap.Put('A', 0);
    b := mmap.HasKey('A');
    expect(b);
  }

  @Test
  method TestDt() {
    var mmap := new MutableMap(p4);
    var b := mmap.HasKey(A);
    expect(!b);
    mmap.Put(A, 0);
    b := mmap.HasKey(A);
    expect(b);
  }

  @Test
  method TestString() {
    var mmap := new MutableMap(p6);
    var b := mmap.HasKey("A");
    expect(!b);
    mmap.Put("A", 0);
    b := mmap.HasKey("A");
    expect(b);
  }

  // does not work everywhere
  // @Test method TestObject() {
  //   var mmap := new MutableMap(p5);
  //   var b := mmap.HasKey(null);
  //   expect(!b);
  //   mmap.Put(null, 0);
  //   b := mmap.HasKey(null);
  //   expect(b);
  // }

}