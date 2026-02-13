/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
 Contains definitions of well-formedness for parsers (stating that they must consume part of their input). 
 */
module Std.JSON.Utils.Parsers {
  import opened BoundedInts
  import opened Wrappers
  import opened Views.Core
  import opened Cursors

  type SplitResult<+T, +R> = Result<Split<T>, CursorError<R>>

  type Parser<!T, +R> = p: Parser_<T, R> | p.Valid?()
      // BUG(https://github.com/dafny-lang/dafny/issues/2103)
    witness ParserWitness<T, R>() // BUG(https://github.com/dafny-lang/dafny/issues/2175)
  datatype Parser_<!T, +R> = Parser(fn: FreshCursor -> SplitResult<T, R>,
                                    ghost spec: T -> bytes) {
    ghost predicate Valid?() {
      forall cs': FreshCursor :: fn(cs').Success? ==> fn(cs').value.StrictlySplitFrom?(cs', spec)
    }
  }

  function ParserWitness<T, R>(): (p: Parser_<T, R>)
    ensures p.Valid?()
  {
    Parser(_ => Failure(EOF), _ => [])
  }

  // BUG(https://github.com/dafny-lang/dafny/issues/2137): It would be much
  // nicer if `SubParser` was a special case of `Parser`, but that would require
  // making `fn` in parser a partial function `-->`.  The problem with that is
  // that we would then have to restrict the `Valid?` clause of `Parser` on
  // `fn.requires()`, thus making it unprovable in the `SubParser` case (`fn`
  // for subparsers is typically a lambda, and the `requires` of lambdas are
  // essentially uninformative/opaque).
  datatype SubParser_<!T, +R> = SubParser(
    ghost cs: Cursor,
    ghost pre: FreshCursor -> bool,
    fn: FreshCursor --> SplitResult<T, R>,
    ghost spec: T -> bytes)
  {
    ghost predicate Valid?() {
      && (forall cs': FreshCursor | pre(cs') :: fn.requires(cs'))
      && (forall cs': FreshCursor | cs'.StrictlySplitFrom?(cs) :: pre(cs'))
      && (forall cs': FreshCursor | pre(cs') :: fn(cs').Success? ==> fn(cs').value.StrictlySplitFrom?(cs', spec))
    }
  }

  type SubParser<!T, +R> = p: SubParser_<T, R> | p.Valid?()
    witness SubParserWitness<T, R>() // BUG(https://github.com/dafny-lang/dafny/issues/2175)

  function SubParserWitness<T, R>(): (subp: SubParser_<T, R>)
    ensures subp.Valid?()
  {
    SubParser(Cursor([], 0, 0, 0),
              (cs: FreshCursor) => false,
              (cs: FreshCursor) => Failure(EOF),
              _ => [])
  }
}