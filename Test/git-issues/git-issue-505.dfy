// RUN: %dafny /compile:0 /timeLimit:20 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma a()
{
  var a: int := 0x0000_0000_DEAD_BEEF;
  var testbv: bv64 := a as bv64;
  var testval: int := testbv as int;

  assert testval == a; // "Timed out on: assertion violation"
}
lemma b()
{
  var a: int := 0x0000_0010_DEAD_BEEF;
  var testbv: bv64 := a as bv64;
  var testval: int := testbv as int;

  assert testval == a; // "Timed out on: assertion violation"
}
lemma c()
{
  var a: int := 0x0000_0000_DEAD_BEEF;
  var testbv: bv32 := a as bv32;
  var testval: int := testbv as int;

  assert testval == a; // "Timed out on: assertion violation"
}
lemma d()
{
  var a: int := 0x0000_0000_0000_BEEF;
  var testbv: bv16 := a as bv16;
  var testval: int := testbv as int;

  assert testval == a; // OK
}
lemma e()
{
  var a: int := 0x0000_0000_0000_00EF;
  var testbv: bv8 := a as bv8;
  var testval: int := testbv as int;

  assert testval == a; // OK
}

// The longer bit vector operations currently timeout (because of Z3's inefficient support for bit-vector/int conversions), 
// but the shorter bit width attempts should verify OK
