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

newtype uint32WithMethods = x: int | 0 <= x < 0x1_00000000 {
  static const zero: uint32WithMethods := 0 as uint32WithMethods
  static const one: uint32WithMethods := zero + 1
  const n: int := this as int
  static function ctor(x: int): uint32WithMethods {
    if 0 <= x < 0x1_00000000 then
      x as uint32WithMethods
    else
      zero
  }
  function plus(y: uint32WithMethods): uint32WithMethods
    requires this as int + y as int < 0x1_00000000
  {
    this + y
  }
  function plus_overflow(y: uint32WithMethods): uint32WithMethods
  {
    (this as bv32 + y as bv32) as uint32WithMethods
  }
  function minus_overflow(y: uint32WithMethods): uint32WithMethods
  {
    (this as bv32 - y as bv32) as uint32WithMethods
  }
  function times_overflow(y: uint32WithMethods): uint32WithMethods
  {
    (this as bv32 * y as bv32) as uint32WithMethods
  }
}

newtype IntWrapper = int {
  const zero := 0 as IntWrapper
  function DoublePlus(plus: IntWrapper): IntWrapper {
    this * 2 + plus + plus.zero.AddZero()
  }
  function AddZero(): IntWrapper {
    this
  }
}
// Ensuring the uint32 is hashable
datatype {:rust_rc false} UInt32Pair = UInt32Pair(first: uint32WithMethods, second: uint32WithMethods)

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

  var three := uint32WithMethods.ctor(3);
  var six := three.plus(three);
  var two := uint32WithMethods.ctor(2);
  var almost_overflow := 0xFFFFFFFF as uint32WithMethods;
  var almost_overflow2 := 0xFFFFFFFE as uint32WithMethods;
  expect two == three.plus_overflow(almost_overflow);
  expect almost_overflow == two.minus_overflow(three);
  expect six == three.times_overflow(two);
  expect almost_overflow2 == almost_overflow.times_overflow(two);
  expect (3 as IntWrapper).DoublePlus(1 as IntWrapper) == 7 as IntWrapper;
}
