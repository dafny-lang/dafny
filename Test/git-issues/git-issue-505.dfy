// RUN: %dafny /compile:0 /timeLimit:20 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

// The longer bit vector operations currently timeout (because of Z3's
// inefficient support for bit-vector/int conversions),
// but the shorter bit width attempts verify OK
