// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --unicode-char=false --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Map<T, U>(m: map<T, U>): map<T, U> {
  m
}

datatype Test_ = Test(i: int) {
  ghost const Valid?: bool := 0 <= i < 4

  predicate Char?(c: char)
    requires Valid?
    requires c as int < 256
  {
    c < 3 as char
  }
}

datatype NeedsTypeParameter_<!T> = NeedsTypeParameter(t: T -> bool)

type NeedsTypeParameter<!T> = x: NeedsTypeParameter_<T> | true witness NeedsTypeParameter((t: T) => false)

type Test = t: Test_ | t.Valid? witness Test(0)

newtype UInt16 = x: int | 0 <= x < 65536

newtype Int16 = x: int | -32768 <= x < 32768

type CodeUnit = bv16

method CharToString(c: char, s: map<char, string>) returns (r: string) {
  if c in s {
    return "inside:" + s[c];
  }
  return "not inside";
}

function LastCharToNat(str: string, digits: map<char, nat>) : (n: nat)
  requires forall c | c in str :: c in digits
{
  if str == [] then 0
  else
    digits[str[|str| - 1]]
}

method Main() {
  var m := Map(map[1 := 2]);
  var s: set<set<int>> := {{}};
  expect |s| == 1;
  var z := (c => c as CodeUnit)('a');
  var t: Test := Test(2);
  var x := CharToString('a', map['a' := "hello"]);
  expect x == "inside:hello";
  var y := CharToString('z', map['a' := "hello"]);
  expect y == "not inside";
  if t.Char?(2 as char) {
    print "Everything is ok.";
  }
}
