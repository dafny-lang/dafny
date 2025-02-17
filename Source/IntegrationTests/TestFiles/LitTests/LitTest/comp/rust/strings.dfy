// NONUNIFORM: Test of the output of the Rust translation
// RUN: %baredafny run --target=rs --enforce-determinism --unicode-char=true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/strings-rust/src/strings.rs" "%S/strings-unicode.check"
// RUN: %baredafny run --target=rs --enforce-determinism --unicode-char=false "%s"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/strings-rust/src/strings.rs" "%S/strings-utf16.check"

newtype uint8 = x: int | 0 <= x < 255
newtype uint7 = x: int | 0 <= x < 128

method Main() {
  print 'H', 'e', "llo\n";
  var x8 := 'H' as uint8;
  var x7 := x8 as uint7;
  print x7;
  var y8 := x7 as uint8;
  var h := y8 as char;
  expect h == 'H';
}