// RUN: %exits-with 4 %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
  const BIG := 16*4*(-2+8-2)*10
  const BYTE_MAX := 16*4*(-2+8-2)
  newtype byte = x | 0 <= x < BYTE_MAX*2/2
  newtype b0 = x | 0 <= x < BIG
  newtype b1 = x | 0 <= x < 11/2
  newtype b2 = x | 0 <= x < 100%15
  newtype b3 = x | 0 <= x < (-100)%15
  newtype b3a = x | 0 <= x < (-100)%-15
  newtype b4 = x | 0 <= x < -((-100)/15)
  newtype b4a = x | 0 <= x < ((-100)/-15)
  newtype b5 = x | 0 <= x < if 1 == 2 then 20 else 42
  newtype b6 = x | 0 <= x < if 1 != 2 then 20 else 42
  newtype b7 = x | 0 <= x < if 1 >= 2 then 20 else 42
  newtype b8 = x | 0 <= x < if 1 <= 2 then 20 else 42
  newtype b9 = x | 0 <= x < if 1 >  2 then 20 else 42
  newtype ba = x | 0 <= x < if 1 <  2 then 20 else 42
  newtype b3b = x | 0 <= x < -((100)/-15)
  newtype b4b = x | 0 <= x < ((100)%-15)
  method m1() {
    var x := 3 as byte; // OK
    var y := 300 as byte; // expected error, to check that byte has a 0..256 range
  }
  method m2() {
    var x2 := 300 as b0; // OK
    var x3 := 300 as b2; // expect error
  }
  method m3() {
    var x3 := 300 as b3; // expect error
  }

  const c0: b1 := 4
  newtype cx = x:int | 0 <= x < c0 as int
}

