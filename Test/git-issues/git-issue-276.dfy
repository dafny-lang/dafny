// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
    const BIG := 16*4*(-2+8-2)*10
    const BYTE_MAX := 16*4*(-2+8-2)
    newtype byte = x | 0 <= x < BYTE_MAX*2/2
    newtype b0 = x | 0 <= x < BIG
    const TR := true
    newtype b2 = x | 0 <= x < (if TR then 10 else 2000)
    newtype b3 = x | 0 <= x < (if 2!=3 && 4<5 then 10 else 2000)
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
}

