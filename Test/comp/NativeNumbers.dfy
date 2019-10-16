// Skip JavaScript because JavaScript doesn't have the same native types

// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
    Int8Test();
    Int16Test();
}

// test handling of byte/short arithmetic in Java
newtype {:nativeType "sbyte"} int8 = x | -0x80 <= x < 0x80
newtype {:nativeType "short"} int16 = x | -0x8000 <= x < 0x8000

method Int8Test() {
  var a, b := 20, 30;
  var r0 := MInt8(a, b);
  var r1 := MInt8(b, a);
  var r2 := MInt8(-2, b);
  print a, " ", b, "\n";
  print r0, " ", r1, " ", r2, "\n";
}

method MInt8(m: int8, n: int8) returns (r: int8) {
  if m < 0 || n < 0 {
    r := 18;
  } else if m < n {
    r := n - m;
  } else {
    r := m - n;
  }
}

method Int16Test() {
  var a, b := 20, 30;
  var r0 := MInt16(a, b);
  var r1 := MInt16(b, a);
  var r2 := MInt16(-2, b);
  print a, " ", b, "\n";
  print r0, " ", r1, " ", r2, "\n";
}

method MInt16(m: int16, n: int16) returns (r: int16) {
  if m < 0 || n < 0 {
    r := 18;
  } else if m < n {
    r := n - m;
  } else {
    r := m - n;
  }
}

