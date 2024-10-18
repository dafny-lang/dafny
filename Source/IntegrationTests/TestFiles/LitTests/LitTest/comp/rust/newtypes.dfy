// RUN: %testDafnyForEachCompiler --type-system-refresh --general-newtypes --refresh-exit-code=0 "%s"

newtype B = bool {
  const b := this as bool
  static const zero := false as B
  static function Zero(): B {
    zero
  }
  const n := Neg()
  function Neg(): B
  {
    !this
  }
  method NegMethod() returns (z: B) {
    z := Neg();
  }
  static method NegMethodStatic(b: B) returns (z: B) {
    z := b.NegMethod();
  }
}
newtype int2 = x: int | -2 <= x < 2 {
  static const zero := 0 as int2
  static function Zero(): int2 {
    zero
  }
  const n := Neg()
  function Neg(): int2
  {
    if this == -2 as int2 then this else -this
  }
  method NegMethod() returns (z: int2) {
    z := Neg();
  }
  static method NegMethodStatic(b: int2) returns (z: int2) {
    z := b.NegMethod();
  }
}
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
  var trueb := true as B;
  print trueb, "=true\n";
  print trueb.b, "=true\n";
  print B.zero, "=false\n";
  print B.Zero(), "=false\n";
  print trueb.n, "=false\n";
  print trueb.Neg(), "=false\n";
  trueb := trueb.NegMethod();
  print trueb, "=false\n";
  trueb := B.NegMethodStatic(trueb);
  print trueb, "=true\n";
  var one := 1 as int2;
  print int2.zero, "=0\n";
  print one, "=1\n";
  print one.n, "=-1\n";
  print int2.Zero(), "=0\n";
  print one.Neg(), "=-1\n";
  one := one.NegMethod();
  print one, "=-1\n";
  one := int2.NegMethodStatic(one);
  print one, "=1\n";
  
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
