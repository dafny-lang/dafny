/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/** The parsers builder DSL but specialized for strings */

module Std.Parsers.StringBuilders refines Builders {
  import P = StringParsers
  export StringBuilders extends Builders
    provides ToInput,
             ToInputEnd,
             S,
             Int,
             Nat,
             WS,
             Except,
             Digit,
             DigitNumber,
             DebugSummaryInput,
             PrintDebugSummaryOutput,
             FailureToString,
             Apply,
             InputToString,
             // Verbose
             String,
             Whitespace

  function ToInput(other: seq<C>): (i: Input)
    ensures P.A.View(i) == other
  {
    P.A.Seq.Slice(other, 0, |other|)
  }

  function ToInputEnd(other: seq<C>, fromEnd: int := 0): (i: Input)
    requires 0 <= fromEnd <= |other|
    ensures P.A.View(i) == other[|other|-fromEnd..|other|]
  {
    P.A.Seq.Slice(other, |other| - fromEnd, |other|)
  }

  /** `S(PREFIX)` returns success on its input if its starts with `PREFIX`,  
      On success, `.value` contains the extracted string. You can ignore it by chaining it like `S(PREFIX).e_I(...)`  
      On failure, returns a recoverable error that did not consume the input.
      Verbose equivalent: `String(PREFIX)`
      */
  function S(s: string): B<string> {
    B(P.String(s))
  }

  /** `String(PREFIX)` is the verbose equivalent of `S(PREFIX)` */
  function String(s: string): B<string> {
    S(s)
  }

  /** `Int` parses any integer.  
      On success, `.value` contains the extracted integer. `.remaining` contains the suffix.  
      On failure, returns a recoverable error that did not consume the input.*/
  const Int: B<int> := B(P.Int())

  /** `Nat` parses any nonnegative integer.  
      On success, `.value` contains the extracted natural integer.  
      On failure, returns a recoverable error that did not consume the input.*/
  const Nat: B<nat> := B(P.Nat())

  /** `Digit` parses any digit.
      On success, `.value` contains the extracted digit as a `char`  
      See `DigitNumber` to obtain a digit as a nat.  
      On failure, returns a recoverable error that did not consume the input.*/
  const Digit: B<char> := B(P.Digit())

  /** `DigitNumber` parses any digit.  
      On success, `.value` contains the digit as a `nat`.  
      See `Digit` to obtain a digit as a char.  
      On failure, returns a recoverable error that did not consume the input.*/
  const DigitNumber: B<nat> := B(P.DigitNumber())

  /** `WS` parses any number of white space characters in "\r\n\t ", and return it as a string.  
      On success, `.value` contains the extracted whitespace. You can ignore it by chaining it like `WS.e_I(...)`  
      Never fails since it can also return an empty string.
      Verbose equivalent: `Whitespace` */
  const WS: B<string> := B(P.WS())

  /** `Whitespace` is the verbose equivalent of `WS`. */
  const Whitespace: B<string> := WS

  /** `Except(CHARACTERS)` parses any number of characters not in the given string.  
      On success, `.value` contains the parsed characters as a `string`.  
      Never fails since it can also return an empty string. */
  function Except(s: string): B<string> {
    CharTest((c: char) => c !in s, "Not '" + s + "'").Rep()
  }

  /** `DebugSummaryInput(name, input)` returns `> {name}: {|input|} "{escape(input[0])}"`
      suitable for debugging what comes into a parser. */
  function DebugSummaryInput(name: string, input: string): string {
    P.DebugSummaryInput(name, input)
  }

  /** PrintDebugSummaryOutput(name, input, result) prints

          < {name}: {|input|} "{escape(input[0])}"
 
      if success, then prints

          | (success)

      if failure, then prints

          | R: {remaining}
      
      if failure and the remaining is smaller than the input, prints

          | Was committed
      
      if failure, then prints

          | ... nice failure message that would be reported.

      This output is suitable suitable for debugging what comes off a parser. */
  method {:print} PrintDebugSummaryOutput<R>(name: string, input: string, result: ParseResult<R>) {
    P.PrintDebugSummaryOutput(name, input, result);
  }

  /** Converts a failure message over the given input into a nice message like:

          .... the line that failed ....
                  ^
          Error: the error message on what was expected.
   */
  function FailureToString<R>(input: string, result: ParseResult<R>): (s: string)
    requires result.IsFailure()
  {
    P.FailureToString(input, result)
  }

  /** Applies a parser to a string and returns the ParseResult */
  function Apply<T>(parser: B<T>, input: string): ParseResult<T> {
    P.Apply(parser.apply, input)
  }

  function InputToString(input: Input): string {
    P.A.View(input)
  }
}