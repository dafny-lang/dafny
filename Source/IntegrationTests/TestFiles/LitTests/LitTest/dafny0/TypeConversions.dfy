// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --relax-definite-assignment --rprint:-


newtype EvenInt = x | x % 2 == 0
newtype SmallReal = r | -4.0 <= r < 300.0

// Use of the following predicate will prevent Boogie's cleverness of discarding assignments to dead variables
ghost predicate UseTheVars(x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0) { true }

method M0() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, b67, w, seven, noll)
{
  if {
    case true                 => n := x as int;  // error: x may be negative
    case 0 <= x                => x := x as int;
    case true                 => x := r as int;  // error: r may have a fractional part
    case true                 => n := r.Floor;  // error: r may be negative
    case 0.0 <= r              => n := r.Floor;
    case r == r.Floor as real => x := r as int;
    case true                 => var b := r as int == r.Floor;  // error: conversion to int may fail
    case true                 => assert -4 <= small.Floor < 300;
    case true                 => even := 6.0 as EvenInt;  assert even == 6;
  }
}

method M1() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, b67, w, seven, noll)
{
  if {
    case true => x := b67 as int;
    case true => x := w as int;
    case true => x := seven as int;
    case true => x := noll as int;
    case true => n := noll as int;
    case true => n := b67 as int;  // note, a bitvector is never negative
    case true => r := b67 as real;
    case true => r := seven as real;
    case true => r := noll as real;
    case true => even := (b67 as int * 2) as EvenInt;
    case true => small := small as real as SmallReal;
    case true => small := small.Floor as SmallReal;
    case true => small := noll as SmallReal;
    case true => small := seven as SmallReal;
    case true => small := w as SmallReal;  // error: w may be too big
    case (w & 0xF) as int <= 0xF /* Z3 doesn't know much about bv2int :( */ => small := (w & 0xF) as SmallReal;
  }
}

method M2() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, b67, w, seven, noll)
{
  if {
    case true => b67 := b67 as bv67;
    case true => b67 := w as bv67;
    case true => b67 := seven as bv67;
    case true => b67 := noll as bv67;
    case true => w := b67 as bv32;  // error: b67 may be too big
    case true => w := w as bv32;
    case true => w := seven as bv32;
    case true => w := noll as bv32;
    case true => seven := b67 as bv7;  // error: b67 may be too big
    case true => seven := w as bv7;  // error: w may be too big
    case true => seven := seven as bv7;
    case true => seven := noll as bv7;
  }
}

method M2'() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, b67, w, seven, noll)
{
  if {
    case true => noll := b67 as bv0;  // error: b67 may be too big
    case true => noll := w as bv0;  // error: w may be too big
    case true => noll := seven as bv0;  // error: seven may be too big
    case true => noll := noll as bv0;
  }
}

method M3() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, b67, w, seven, noll)
{
  if {
    case true => x, r := b67 as int, b67 as real;
    case true => x, r := w as int, w as real;
    case true => x, r := seven as int, seven as real;
    case true => x, r := noll as int, noll as real;
  }
  assert 0 <= x && 0.0 <= r;
}
// M4 is checked quickly, but using bv67 instead of bv7 takes forever, and even bv23 takes 40 minutes. See numbers at bottom of this file.
method M4() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, seven as bv67, w, seven, noll)
{
  if {
    case true => even := noll as EvenInt;
    case true => even := seven as EvenInt;  // error: "seven" may be odd
    case seven as int % 2 == 0 => even := seven as EvenInt;
    case true => small := seven as SmallReal;
    case true =>
      even := small as EvenInt;  // error (x2): small may not even be an integer, let alone odd
    case small == small.Floor as SmallReal =>
      even := small as EvenInt;  // error: small may be odd
    case small == small.Floor as SmallReal && small as int % 2 == 0 =>
      even := small as EvenInt;
  }
}

method M5() returns (x: int, n: nat, r: real, even: EvenInt, small: SmallReal, b67: bv67, w: bv32, seven: bv7, noll: bv0)
  ensures UseTheVars(x, n, r, even, small, b67, w, seven, noll)
{
  x := 150;
  if {
    case true => b67 := x as bv67;
    case true => w := x as bv32;
    case true => seven := x as bv7;  // error: 'x' may not fit in 7 bits
    case true => noll := x as bv0;  // error: 'x' may not fit in 0 bits
    case n < 128 => seven := n as bv7;
    case n == 0 => noll := n as bv0;
    case n < 1 => noll := n as bv0;
    case 0 <= even < 0x1_0000_0000 => w := even as bv32;
    case small as real == small.Floor as real => seven := (if 0.0 <= small < 100.0 then small else 100.0) as bv7;
  }
}

class Class { }
type ClassSubset = c: Class | true // error: the witness guess "null" is not good enough


/***
  Conversions between integers and bitvectors and their corresponding operations is tough for Z3.
  Given the template program program:

      type BvType = bv67;

      function {:bvbuiltin "bvurem"} BvMod(BvType, BvType): BvType;

      function {:bvbuiltin "bv2int"} BvToNat(BvType): int;

      procedure M4(b: BvType)
      {
        assume BvToNat(b) mod 2 == 0;
        assert BvMod(b, 2bv67) == 0bv67;
      }

  which is an extract from method M4 above, and replacing the three occurrences of "67" with numbers starting
  from "6", Z3 version 4.12.1 requires the following times:
     
      --------------- bv6 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.25s user 0.08s system 100% cpu 0.336 total
      --------------- bv7 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.24s user 0.08s system 100% cpu 0.322 total
      --------------- bv8 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.27s user 0.09s system 100% cpu 0.359 total
      --------------- bv9 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.25s user 0.08s system 101% cpu 0.319 total
      --------------- bv10 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.25s user 0.08s system 100% cpu 0.329 total
      --------------- bv11 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.26s user 0.08s system 101% cpu 0.334 total
      --------------- bv12 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.26s user 0.09s system 100% cpu 0.347 total
      --------------- bv13 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.28s user 0.08s system 100% cpu 0.363 total
      --------------- bv14 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.33s user 0.09s system 100% cpu 0.420 total
      --------------- bv15 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.42s user 0.09s system 100% cpu 0.504 total
      --------------- bv16 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.67s user 0.08s system 100% cpu 0.739 total
      --------------- bv17 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  1.31s user 0.09s system 100% cpu 1.399 total
      --------------- bv18 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.24s user 0.08s system 10% cpu 3.194 total
      --------------- bv19 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.26s user 0.09s system 3% cpu 8.910 total
      --------------- bv20 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.25s user 0.08s system 1% cpu 30.118 total
      --------------- bv21 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.28s user 0.11s system 0% cpu 2:15.97 total
      --------------- bv22 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.35s user 0.18s system 0% cpu 10:31.82 total
      --------------- bv23 --------------

      Boogie program verifier finished with 1 verified, 0 errors
      boogied dd.bpl  0.45s user 0.44s system 0% cpu 39:51.32 total

  This shows at least exponential growth.

***/
