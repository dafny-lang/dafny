// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

newtype int2 = x: int | -2 <= x < 2
newtype int16 = x: int | -32768 <= x < 32768
const INT2_MAX: int2 := 1
type zero = x: int2 | x == 0 witness 0
const Zero: zero := 0
const DChar : char := 68 as char
type CodeUnit = bv8
const cu: CodeUnit := 0
newtype uint8  = x: int | 0 <= x < 0x100
type byte = uint8
newtype uint32 = x: int | 0 <= x < 0x1_00000000

method Main(){
  print INT2_MAX as int, "\n";
  print Zero as int16, "\n";
  print DChar, "\n";
  print [0, 1, 2][Zero], "\n";
  print [0, 1, 2][Zero..INT2_MAX], "\n";
  var f: CodeUnit -> byte := c => c as byte;
  var arr := new bool[INT2_MAX];
  print arr.Length, "\n";
  print DChar as uint32, "\n";
}
