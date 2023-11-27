module ArithmeticTests {
  import opened DafnyStdLibs.Arithmetic.Logarithm
  import opened DafnyStdLibs.Arithmetic.Power
  import opened DafnyStdLibs.Arithmetic.Mul
  import opened DafnyStdLibs.Arithmetic.Power2
  import opened DafnyStdLibs.Arithmetic.MulInternals
  import opened DafnyStdLibs.Arithmetic.ModInternals
  import opened DafnyStdLibs.Arithmetic.DivInternals

  method {:test} TestMul() {
    for i := -10 to 10 {
      for j := -10 to 10 {
        expect MulRecursive(i, j) == i * j;
      }
    }
  }

  method {:test} TestPowLog() {
    expect Pow(-4, 0) == 1;
    expect Pow(-2, 2) == 4;
    expect Pow(-2, 3) == -8;
    expect Pow2(3) == 8;

    expect Log(5, 0) == 0;
    expect Log(2, Pow2(5)) == 5;
  }

  method {:test} TestDiv() {
    expect DivRecursive(5, 3) == 1;
    expect DivRecursive(-3, 5) == -1;
    expect DivRecursive(-3, -5) == 1;
  }

  method {:test} TestMod() {
    expect ModRecursive(5, 3) == 2;
    expect ModRecursive(-3, 5) == 2;
  }
}