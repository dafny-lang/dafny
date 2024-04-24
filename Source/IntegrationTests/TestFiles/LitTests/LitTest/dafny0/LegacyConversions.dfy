// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --relax-definite-assignment --general-newtypes=false

module Chars {
  type MyChar = ch: char | ch != 'b'
  type Char = char

  type CharSubset = ch: char | ch != 'b'

  method CharConversions() returns (s: CharSubset, x: MyChar, y: Char, a: char) {
    if
    case true =>
      a := a as char;
    case true =>
      a := a as CharSubset; // error: may violate constraint
    case true =>
      x := a as MyChar; // error: may violate constraint
    case true =>
      y := a as Char;
    case true =>
      x := y as MyChar; // error: may violate constraint
  }

  type BV = b: bv6 | b != 23
  type JustBv6 = b: bv6 | true
  type Word = bv32
  type Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  type NotSpace = ch: char | ch != ' '

  method CharBv() returns (ch: char, nr: NotSpace, a: bv6, x: BV, big: Big, i: int) {
    if
    case 0 <= i < 100 =>
      nr := i as NotSpace; // error: might be space
    case true =>
      ch := nr as char;
    case true =>
      nr := ch as NotSpace; // error: might be space
    case true =>
      nr := a as NotSpace; // error: might be space
    case true =>
      nr := x as NotSpace; // error: might be space
  }

  method ConvertBV() returns (s: BV, s': JustBv6, x: BV, y: Word, z: Big, a: bv6, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    if
    case true =>
      x := y as BV; // error (x2): might be 23 and might be too big
    case y < 30 =>
      x := y as BV; // error: might be 23
    case 30 <= y =>
      x := y as BV; // error: might be too big
    case y < 20 =>
      x := y as BV;
  }
  
  method Conversions0() returns (s: BV, s': JustBv6, x: BV, y: Word, z: Big, a: bv6, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    if
    case true =>
      a := b as bv6; // error: might be too big
    case b < 64 =>
      a := b as bv6;
    case s' != 23 =>
      s := s' as BV;
    case true =>
      s := y as BV; // error (x2): might be 23 and might be too big
    case true =>
      s' := s as JustBv6;
    case true =>
      s := s' as BV; // error: might violate constraint
    case true =>
      y := x as Word;
    case true =>
      b := y as bv32;
    case true =>
      y := b as Word;
  }
  
  method Conversions1() returns (s: BV, s': JustBv6, x: BV, y: Word, z: Big, a: bv6, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    if
    case true =>
      a := b as BV; // error (x2): might not fit and might violate constraint
    case true =>
      x := b as BV; // error (x2): might not fit and might violate constraint
  }
  
  method Conversions2() returns (s: BV, s': JustBv6, x: BV, y: Word, z: Big, a: bv6, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    if
    case b != 23 =>
      a := b as BV; // error: might not fit
    case b < 64 =>
      a := b as BV; // error: might violate constraint
    case 23 != b < 64 =>
      a := b as BV;
    case 25 <= b < 50 =>
      x := b as BV;
  }
}

module CharSize {
  type Big = b: bv1024 | true

  type NotSpace = ch: char | ch != ' '
  type AnyChar = ch: char | true

  method CharBigBv() returns (big: Big, nr: NotSpace, ac: AnyChar) {
    if 
    case true =>
      nr := big as NotSpace; // error (x2): might be too big and might violate constraint
    case true =>
      ac := big as AnyChar; // error: might be too big
  }
}
