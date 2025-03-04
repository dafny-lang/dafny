// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=true --general-newtypes=false

method Main() {
  Is.Test();
}

module Is {
  method Test() {
    FromReal();
    ToChar();
    ToBitvector();
    ToNative();
  }

  method FromReal() {
    var r: real;
    r := 3.14;
    print r is int, " "; // false
    print r is bv32, " "; // false
    print r is bv1, " "; // false
    print r is ORDINAL, "\n"; // false
    r := 3.0;
    print r is int, " "; // true
    print r is bv32, " "; // true
    print r is bv1, " "; // false
    print r is ORDINAL, "\n"; // true
  }

  method ToChar() {
    var x: int;
    var y: bv71;
    var z: bv16;

    x, y, z := 65, 65, 65;
    print x is char, " "; // true
    print y is char, " "; // true
    print z is char, "\n"; // true

    x, y, z := 0xD912, 0xD912, 0xD912;
    print x is char, " "; // false
    print y is char, " "; // false
    print z is char, "\n"; // false

    x, y := 0x20_0000, 0x20_0000;
    print x is char, " "; // false
    print y is char, "\n"; // false

    print 0xD7FF is char, " "; // true
    print 0xD800 is char, " "; // false
    print 0xD801 is char, " "; // false
    print 0xDFFF is char, " "; // false
    print 0xE000 is char, " "; // true
    print 0xE001 is char, " "; // true
    print 0x10_FFFF is char, " "; // true
    print 0x11_0000 is char, " "; // false
    print 0x11_0001 is char, "\n"; // false
  }

  method ToBitvector() {
    var x: int;
    x := 0;
    print x is bv0, " ", x is bv5, " ", x is bv31, " ", x is bv32, " ", x is bv700, "\n"; // true true true true true
    x := 90;
    print x is bv0, " ", x is bv5, " ", x is bv31, " ", x is bv32, " ", x is bv700, "\n"; // false false true true true
    x := -0x8000_0000;
    print x is bv0, " ", x is bv5, " ", x is bv31, " ", x is bv32, " ", x is bv700, "\n"; // false false false false fals
    x := 0x8000_0000;
    print x is bv0, " ", x is bv5, " ", x is bv31, " ", x is bv32, " ", x is bv700, "\n"; // false false false true true

    var y: bv32;
    y := 0x8000_0000;
    print y is bv0, " ", y is bv5, " ", y is bv31, " ", y is bv32, " ", y is bv700, "\n"; // false false false true true
  }

  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
  newtype uint32 = x: int | 0 <= x < 0x1_0000_0000

  method ToNative() {
    var x: int;
    x := 0;
    print x is int32, " ", x is uint32, " "; // true true
    x := 90;
    print x is int32, " ", x is uint32, "\n"; // true true
    x := -0x8000_0000;
    print x is int32, " ", x is uint32, " "; // true false
    x := 0x8000_0000;
    print x is int32, " ", x is uint32, "\n"; // false true

    var y: bv31;
    y := 0x7FFF_FFFF;
    print y is int32, " ", y is uint32, " "; // true true
    print (y + 1) is int32, " ", (y + 1) is uint32, "\n"; // true true (because y+1 wraps around in bv31)

    var z: bv32;
    z := 0x7FFF_FFFF;
    print z is int32, " ", z is uint32, " "; // true true
    z := 0x8000_0000;
    print z is int32, " ", z is uint32, "\n"; // false true
  }
}
