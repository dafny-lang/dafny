// RUN: %baredafny run %args --target=cpp "%s" ExternDefs.h > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "Extern"} Extern {
  newtype uint64 = i:int | 0 <= i < 0x10000000000000000

  method {:extern "Extern", "Caller"} Caller(inc:uint64-->uint64, x:uint64) returns (y:uint64)
    requires inc.requires(x)

  method {:extern "Extern", "GenericCaller"} GenericCaller<A>(inc:A-->A, x:A) returns (y:A)
    requires inc.requires(x)

  class {:extern} GenericClass<A>
  {
    constructor {:extern "Extern", "GenericClass"} (inc:A-->A, x:A)
      requires inc.requires(x)

    method {:extern "Extern", "get"} get() returns (y:A)
  }
}

module Test {
  import opened Extern

  newtype uint32  = i:int | 0 <= i < 0x100000000

  // Function-method tests
  function method Test(x:uint32) : uint64 {
    x as uint64 + 1
  }

  function method Seqs<T>(s:seq<T>, x:uint32, default_val:T) : T
    requires |s| < 1000
  {
    if |s| as uint32 > x then s[x] else default_val
  }

  // Function pointer tests
  function method AddOne(x:uint64) : uint64
    requires x < 100
  {
    x + 1
  }

  method CallTest() {
    var x := Caller(AddOne, 5);
    print x, "\n";
    var y := GenericCaller(AddOne, 6);
    print y, "\n";
    var c := new GenericClass(AddOne, 7);
    var z := c.get();
    print z, "\n";
  }


  method Main() {
    var y := Test(12);  // Basic function-method test
    CallTest();         // Function pointer tests
    print y, "\n";
  }
}

