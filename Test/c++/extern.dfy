
module Extern {
  newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000

  method {:extern "Extern", "newArrayFill"} newArrayFill<T>(n: uint64, t: T) returns (ar: array<T>)
}

module TestMod {
  import opened Extern

  method Test() {
    var a:array<uint64> := newArrayFill(5, 42);
  }
}
