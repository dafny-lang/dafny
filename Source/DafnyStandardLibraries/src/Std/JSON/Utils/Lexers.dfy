/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Contains a state machine that recognizes quoted strings and skips over backslash-escaped quotes.
 */
module Std.JSON.Utils.Lexers {
  module Core {
    import opened Wrappers
    import opened BoundedInts

    datatype LexerResult<+T, +R> =
        // A Lexer may return three results:
      | Accept // The input is valid.
      | Reject(err: R) // The input is not valid; `err` says why.
      | Partial(st: T) // More input is needed to finish lexing.

    type Lexer<!T, +R> = (T, opt_byte) -> LexerResult<T, R>
  }

  module Strings {
    import opened Core
    import opened BoundedInts

    type StringBodyLexerState = /* escaped: */ bool
    const StringBodyLexerStart: StringBodyLexerState := false

    function StringBody<R>(escaped: StringBodyLexerState, byte: opt_byte)
      : LexerResult<StringBodyLexerState, R>
    {
      if byte == '\\' as opt_byte then Partial(!escaped)
      else if byte == '\"' as opt_byte && !escaped then Accept
      else Partial(false)
    }

    datatype StringLexerState = Start | Body(escaped: bool) | End
    const StringLexerStart: StringLexerState := Start

    function String(st: StringLexerState, byte: opt_byte)
      : LexerResult<StringLexerState, string>
    {
      match st
      case Start() =>
        if byte == '\"' as opt_byte then Partial(Body(false))
        else Reject("String must start with double quote")
      case End() =>
        Accept
      case Body(escaped) =>
        if byte == '\\' as opt_byte then Partial(Body(!escaped))
        else if byte == '\"' as opt_byte && !escaped then Partial(End)
        else Partial(Body(false))
    }
  }
}