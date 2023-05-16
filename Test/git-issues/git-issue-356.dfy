// RUN: %dafny /compile:0 /unicodeChar:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  type Tx = i: int | 0 <= i <= 100
  newtype Tr = r: real | r == r.Floor as real && 0.0 <= r <= 100.0

  method Main() {
    var ch0 := Test0a('a');
    var ch1 := Test0b(100);
    var cInput0, cInput1 := GetTest0cInput();
    var ch2 := Test0c(cInput0, cInput1);
    var ch3 := Test0d();
    var ch4 := Test0e();
    print ch0, " ", ch1, " ", ch2 as int, " ", ch3, " ", ch4, "\n";

    Test1a(0xDEAD, 100, 'a');
    Test1b(0xDEAD, 100, 'a');
    Test1c(0xDEAD, 100, 'a');
    Test1d(0xDEAD, 100, 'a');

    Test2a(42, 'Z');
    Test2b(0x40, 42, 'Z', 70.0, 35);
    Test2c(0x40, 42, 'Z', 70.0, 35, 50);
    Test2d(0x40, 42, 'Z', 70.0, 35, 50, 61.0);

    Test3a('*');
    Test3b(0x0);
    Test3c(50, 50.0, 30);

    print "END\n";
  }

  type bv = bv8
  const mx: int := 256 // limit for the chosen bit-vector type
  const mxch: int := 0x1_0000

  method Test0a(c: char) returns (ch: char)
  {
    ch := c as char;
  }

  method Test0b(n: nat) returns (ch: char)
    requires n < mxch
  {
    ch := n as char;
  }

  method Test0c(b: bv32, ghost c: char) returns (ch: char)
    // The next line says that b is in the range of a char.
    requires c as int as bv32 == b
    // The next line also says that. However, it causes the SMT query
    // to use the (_ int2bv 32) function, which causes Z3 to be
    // extremely slow (several minutes to process this simple method).
    // The problem can be mitigated by using synonyms for the bitvector
    // function. Until those functions are in place, we use the line
    // above instead of the line below as the precondition for this
    // method.pp
    // requires b < mxch as bv32  // in range of char
  {
    ch := b as char;
  }

  method GetTest0cInput() returns (b: bv32, ghost c: char)
    ensures c as int as bv32 == b
  {
    c := '\uDEAD';
    var x: int := 0xDEAD;
    assert c as int == x;
    b := x as bv32;
  }

  //Test0c(0xDEAD, '\uDEAD')


  method Test0d() returns (ch: char)
  {
    var r: real := 42.0;
    ch := r as char;
  }

  method Test0e() returns (ch: char)
  {
    var o: ORDINAL := 42 as ORDINAL;
    ch := o as char;
  }

  method Test1a(b: bv32, n: nat, c: char)
    requires b < mxch as bv32  // in range of char
    requires n < mxch
  {
    var r: real := 42.0;
    var o: ORDINAL := 42 as ORDINAL;

    var nn: int;
    var nnn: int;
    nn := c as int;
    nn := r as int;
    nn := b as int;
    nn := nnn as int;
    nn := o as int;
  }

  method Test1b(b: bv32, n: nat, c: char)
    requires b < mxch as bv32  // in range of char
    requires n < mxch
  {
    var r: real := 42.0;
    var o: ORDINAL := 42 as ORDINAL;

    var rr: real;
    rr := c as real;
    rr := n as real;
    rr := b as real;
    rr := r as real;
    rr := o as real;
  }

  method Test1c(b: bv32, n: nat, c: char)
    requires b < mxch as bv32  // in range of char
    requires n < mxch
  {
    var r: real := 42.0;
    var o: ORDINAL := 42 as ORDINAL;

    var bb: bv32;
    bb := c as bv32;
    bb := n as bv32;
    bb := r as bv32;
    bb := b as bv32;
    bb := o as bv32;
  }

  method Test1d(b: bv32, n: nat, c: char)
    requires b < mxch as bv32  // in range of char
    requires n < mxch
  {
    var r: real := 42.0;
    var o: ORDINAL := 42 as ORDINAL;

    var oo: ORDINAL;
    oo := c as ORDINAL;
    oo := n as ORDINAL;
    oo := r as ORDINAL;
    oo := b as ORDINAL;
    oo := o as ORDINAL;
  }

  method Test2a(n: int, c: char) {
    assert c == c as char;
    expect c == c as char;
    assert c == c as int as char;
    expect c == c as int as char;
    assert c == c as real as char;
    expect c == c as real as char;
    // assert c == c as bv as char; // in Test3
    // expect c == c as bv as char; // in Test3
    assert c == c as ORDINAL as char;
    expect c == c as ORDINAL as char;
    if c as int < mx {
      print c as char, " ", c as int, " ", c as real, " ", c as bv, " ", c as ORDINAL, "\n";
    }

    // assert b == b as bv; // in Test3
    // expect b == b as bv; // in Test3
    // assert b == b as char as bv; // in Test3
    // expect b == b as char as bv; // in Test3
    // assert b == b as int as bv; // in Test3
    // expect b == b as int as bv; // in Test3
    // assert b == b as real as bv; // in Test3
    // expect b == b as real as bv; // in Test3
    // assert b == b as ORDINAL as bv; // in Test3
    // expect b == b as ORDINAL as bv; // in Test3

    assert n == n as int;
    expect n == n as int;
    assert 0 <= n < mxch ==> n == n as char as int;
    expect 0 <= n < mxch ==> n == n as char as int;
    // assert 0 <= n < mx ==> n == n as bv as int; // in Test3
    // expect 0 <= n < mx ==> n == n as bv as int; // in Test3
    assert n == n as real as int;
    expect n == n as real as int;
    assert 0 <= n ==> n == n as ORDINAL as int;
    expect 0 <= n ==> n == n as ORDINAL as int;
    if 0 <= n < mx && n < mxch {
      print n as char, " ", n as int, " ", n as real, " ", n as bv, " ", n as ORDINAL, "\n";
    }
  }

  method Test2b(b: bv, n: int, c: char, r: real, o: ORDINAL) {
    assert r == r as real;
    expect r == r as real;
    assert r == r.Floor as real  ==> 0.0 <= r < (mxch as real) ==> r == r as char as real;
    expect r == r.Floor as real  ==> 0.0 <= r < (mxch as real) ==> r == r as char as real;
    assert r == r.Floor as real  ==> r == r as int as real;
    expect r == r.Floor as real  ==> r == r as int as real;
    // assert r == r.Floor as real ==> 0.0 <= r < (mx as real) ==> r == r as bv as real; // in Test3
    // expect r == r.Floor as real ==> 0.0 <= r < (mx as real) ==> r == r as bv as real; // in Test3
    assert r == r.Floor as real  ==> 0.0 <= r ==> r == r as ORDINAL as real;
    expect r == r.Floor as real  ==> 0.0 <= r ==> r == r as ORDINAL as real;
    if r == r.Floor as real && 0.0 <= r < (mx as real) && r < (mxch as real) {
      print r as char, " ", r as int, " ", r as real, " ", r as bv, " ", r as ORDINAL, "\n";
    }

    assert o == o as ORDINAL;
    expect o == o as ORDINAL;
    assert o.IsNat && o as int < mxch ==> o == o as char as ORDINAL;
    expect o.IsNat && o as int < mxch ==> o == o as char as ORDINAL;
    assert o.IsNat ==> o == o as int as ORDINAL;
    expect o.IsNat ==> o == o as int as ORDINAL;
    assert o.IsNat ==> o == o as real as ORDINAL;
    expect o.IsNat ==> o == o as real as ORDINAL;
    // assert o.IsNat && o as int < mx ==> o == o as bv as ORDINAL; // in Test3
    // expect o.IsNat && o as int < mx ==> o == o as bv as ORDINAL; // in Test3
    if o.IsNat && o as int < mx && o as int < mxch {
      print o as char, " ", o as int, " ", o as real, " ", o as bv, " ", o as ORDINAL, "\n";
    }
  }
  
  method Test2c(b: bv, n: int, c: char, r: real, o: ORDINAL, x: Tx) {
    // subset type
    var nnn: int := x; // Implicit conversion allowed
    assert x == x as Tx;
    expect x == x as Tx;
    assert x == x as char as Tx;
    expect x == x as char as Tx;
    assert x == x as int as Tx;
    expect x == x as int as Tx;
    assert x == x as real as Tx;
    expect x == x as real as Tx;
    assert x == x as bv as Tx;
    expect x == x as bv as Tx;
    assert x == x as ORDINAL as Tx;
    expect x == x as ORDINAL as Tx;
    assert c as int <= 100 ==> c == c as Tx as char;
    expect c as int <= 100 ==> c == c as Tx as char;
    assert 0 <= n as int <= 100 ==> n == n as Tx as int;
    expect 0 <= n as int <= 100 ==> n == n as Tx as int;
    assert r == r.Floor as real &&  0.0 <= r <= 100.0 ==> r == r as Tx as real;
    expect r == r.Floor as real &&  0.0 <= r <= 100.0 ==> r == r as Tx as real;
    assert b as int <= 100 ==> b == b as Tx as bv;
    expect b as int <= 100 ==> b == b as Tx as bv;
    assert o.IsNat && o as int <= 100 ==> o == o as Tx as ORDINAL;
    expect o.IsNat && o as int <= 100 ==> o == o as Tx as ORDINAL;
  }

  method Test2d(b: bv, n: int, c: char, r: real, o: ORDINAL, x: Tx, h: Tr) {
    assert h == h as Tr;
    expect h == h as Tr;
    assert h == h as Tx as Tr;
    expect h == h as Tx as Tr;
    assert h == h as char as Tr;
    expect h == h as char as Tr;
    assert h == h as int as Tr;
    expect h == h as int as Tr;
    assert h == h as real as Tr;
    expect h == h as real as Tr;
    assert h == h as bv8 as Tr;
    expect h == h as bv8 as Tr;
    assert h == h as ORDINAL as Tr;
    expect h == h as ORDINAL as Tr;
    assert x == x as Tr as Tx;
    expect x == x as Tr as Tx;
    assert c as int <= 100 ==> c == c as Tr as char;
    expect c as int <= 100 ==> c == c as Tr as char;
    assert 0 <= n as int <= 100 ==> n == n as Tr as int;
    expect 0 <= n as int <= 100 ==> n == n as Tr as int;
    assert r == r.Floor as real && 0 <= r as int <= 100 ==> r == r as Tr as real;
    expect r == r.Floor as real && 0 <= r as int <= 100 ==> r == r as Tr as real;
    assert b as int <= 100 ==> b == b as Tr as bv8;
    expect b as int <= 100 ==> b == b as Tr as bv8;
    assert o.IsNat && o as int <= 100 ==> o == o as Tr as ORDINAL;
    expect o.IsNat && o as int <= 100 ==> o == o as Tr as ORDINAL;
  }

  // These take a while depending on the width of the bit-vector type
  // About 25 sec on my machine for bv8; longer than I wanted to wait (>10s min) for bv16
  method Test3a(c: char) {
    assert c as int < mx ==> c == c as bv as char;
    expect c as int < mx ==> c == c as bv as char;
  }

  method Test3b(b: bv) {
    assert b == b as bv;
    expect b == b as bv;
    assert b == b as bv32 as bv; // assumes bv32 is at least as wide as bv
    expect b == b as bv32 as bv; // assumes bv32 is at least as wide as bv
    assert b as int < mxch ==> b == b as char as bv;
    expect b as int < mxch ==> b == b as char as bv;
    assert b == b as int as bv;
    expect b == b as int as bv;
    assert b == b as real as bv;
    expect b == b as real as bv;
    assert b == b as ORDINAL as bv;
    expect b == b as ORDINAL as bv;
  }

  method Test3c(n: int, r: real, o: ORDINAL) {
    assert 0 <= n < mx ==> n == n as bv as int;
    expect 0 <= n < mx ==> n == n as bv as int;

    assert r == r.Floor as real ==> 0.0 <= r < (mx as real) ==> r == r as bv as real;
    expect r == r.Floor as real ==> 0.0 <= r < (mx as real) ==> r == r as bv as real;

    assert o.IsNat && o as int < mx ==> o == o as bv as ORDINAL;
    expect o.IsNat && o as int < mx ==> o == o as bv as ORDINAL;
  }
}
