/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module ExampleParsers.AdventOfCode1 {
  import opened Std.Parsers.StringBuilders

  const nonDigit :=
    Except("0123456789\r\n").Rep()

  const parseLine :=
    nonDigit.e_I(DigitNumber).Then(
      (first: nat) =>
        nonDigit.e_I(DigitNumber).??().RepFold(
          (first, first),
          (pair: (nat, nat), newDigit: nat) => (pair.0, newDigit)
        )).I_e(nonDigit)

  const parseInput :=
    parseLine.I_e(S("\r").?().e_I(S("\n").?()))
    .RepFold(0, (acc: int, newElem: (nat, nat)) =>
               acc + newElem.0 * 10 + newElem.1)

  method {:test} TestParser() {
    var input := @"1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet";
    expect Apply(parseInput, input) == ParseResult.ParseSuccess(142, ToInputEnd(input));
  }
}