// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AA {
  method M()
  {
    var m := map[];  // error: underspecified type
  }

  method N()
  {
    var n := multiset{};  // error: underspecified type
  }

  method O()
  {
    var o := [];  // error: underspecified type
  }

  method P()
  {
    var p := {};  // error: underspecified type
  }

  method Q()
  {
    assert (((map[]))) == (((((map[])))));  // error: underspecified type (but not 10 errors)
  }
}

module BB {
  newtype byte = x | 0 <= x < 256

  method B0() returns (s: seq<byte>) {
    s := [10, 20];
  }

  method B1() returns (s: seq<byte>) {
    var b := 10;  // int
    var u: int := 30;
    var t := [b, 20, u];  // error: type mismatch
    s := t;
  }

  method B2() returns (s: seq<byte>) {
    var b := 10;  // byte
    var t := [b, 20];  // seq<byte>
    s := t;
  }

  method B3() returns (s: seq<byte>) {
    var b := 10;  // byte
    var t := [20, b];  // seq<byte>
    s := t;
  }
}

module CC {
  newtype byte = x | 0 <= x < 256

  method M(bytes: seq<byte>) returns (yn: bool)
  {
    var bbb := [1];
    var bb: seq<byte> := [1];
    var sq := [1];
    if
    case true =>  yn := bytes == sq;
    case true =>  yn := bytes == [1];
    case 8 <= |bytes| =>  yn := bytes[0..8] == [0, 0, 0, 0, 0, 0, 0, 2];
    case true =>
      var ints: seq<int>;
      var cmp := [2, 0];  // seq<int>
      yn := ints == cmp;
      yn := bytes == cmp;  // error: mismatched types
  }
}
