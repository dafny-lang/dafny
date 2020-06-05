// RUN: %dafny -compile:4 -compileTarget:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype {:nativeType "byte"} uint8 = x:int | 0 <= x < 0x100
newtype {:nativeType "int"} int32 = x:int | -0x8000_0000 <= x < 0x8000_0000

method Main() {
  var u8 : uint8 := 140;
  var i32 : int32 := u8 as int32;
  print u8, " == ", i32, "\n";
}
