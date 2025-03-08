module ExampleParsers.AdventOfCode1 {
  import opened Std.Parsers.StringBuilders

  const nonDigit :=
    Except("0123456789\r\n").Rep()

  const digit :=
    B(P.DigitNumber())

  const parseLine :=
    nonDigit.e_I(digit).Bind(
      (first: nat) =>
        nonDigit.e_I(digit).??().Rep(
          (first, first),
          (pair: (nat, nat), newDigit: nat) => (pair.0, newDigit)
        )).I_e(nonDigit)

  const parseInput :=
    parseLine.I_e(S("\r").?().e_I(S("\n").?()))
    .Rep(0, (acc: int, newElem: (nat, nat)) =>
           acc + newElem.0 * 10 + newElem.1)

  method {:test} TestParser() {
    var input := @"1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet";
    expect parseInput.apply(input) == P.Success(142, []);
  }
}