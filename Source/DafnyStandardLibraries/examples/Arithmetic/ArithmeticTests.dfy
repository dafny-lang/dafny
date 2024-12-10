module ArithmeticTests {
  import opened Std.Arithmetic.Logarithm
  import opened Std.Arithmetic.Power
  import opened Std.Arithmetic.Mul
  import opened Std.Arithmetic.Power2
  import opened Std.Arithmetic.MulInternals
  import opened Std.Arithmetic.ModInternals
  import opened Std.Arithmetic.DivInternals

  @Test
  method TestMul() {
    for i := -10 to 10 {
      for j := -10 to 10 {
        expect MulRecursive(i, j) == i * j;
      }
    }
  }

  @Test
  @IsolateAssertions
  method TestPowLog() {
    expect Pow(-4, 0) == 1;
    expect Pow(-2, 2) == 4;
    expect Pow(-2, 3) == -8;
    expect Pow2(3) == 8;

    expect Log(5, 0) == 0;
    expect Log(2, Pow2(5)) == 5;
  }

  @Test
  method TestDiv() {
    expect DivRecursive(5, 3) == 1;
    expect DivRecursive(-3, 5) == -1;
    expect DivRecursive(-3, -5) == 1;
  }

  @Test
  method TestMod() {
    expect ModRecursive(5, 3) == 2;
    expect ModRecursive(-3, 5) == 2;
  }
}