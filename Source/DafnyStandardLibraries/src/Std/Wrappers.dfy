/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/** This module provides various kinds of failure-compatible datatypes, including Option.
- Option<R> (Some or None) with a type parameter R that is the type of the Some value
- Outcome<E> (Pass or Fail) with a type parameter E that is the type of a failure value
- Result<R,E> which has both a value type and a failure type
All three of these may be used with `:-` as Dafny failure-compatible types

The module also defines two forms of `Need`, that check the truth of a predicate and
return a failure value if false.
 */
module Std.Wrappers {

  /** This datatype is the conventional Some/None datatype that is often used
      in place of a reference or null.
   */
  datatype Option<+T> = None | Some(value: T) {

    /** True if is None */
    predicate IsFailure() {
      None?
    }

    /** Converts a None result to an Option value with a different value type. */
    function PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }

    /** Returns the value encapsulated in Some */
    function Extract(): T
      requires Some?
    {
      value
    }

    /** Returns the value encapsulated in Some or a default value if None */
    function GetOr(default: T): T {
      match this
      case Some(v) => v
      case None() => default
    }

    /** Converts the datatype value to a Result value (with the given error value) */
    function ToResult<E>(error: E): Result<T, E> {
      match this
      case Some(v) => Success(v)
      case None() => Failure(error)
    }

    /** Converts the datatype value to an Outcome value (with the given error value) */
    function ToOutcome<E>(error: E): Outcome<E> {
      match this
      case Some(v) => Pass
      case None() => Fail(error)
    }

    /** Applies the given function to convert the Option to something else  */
    function Map<FC>(rewrap: Option<T> -> FC): FC
    {
      rewrap(this)
    }
  }

  /** A Success/Failure failure-compatible datatype that carries either a success value or an error value */
  datatype Result<+R, +E> = | Success(value: R) | Failure(error: E) {

    /** True if is Failure */
    predicate IsFailure() {
      Failure?
    }

    /** Converts a Failure value to an alternate Result that has a different value type but the same error type */
    function PropagateFailure<U>(): (r: Result<U, E>)
      requires Failure?
    {
      Failure(this.error)
    }

    /** Returns the value encapsulated in Success */
    function Extract(): R
      requires Success?
    {
      value
    }

    /** Returns the value encapsulated in Success or a default value if Failure */
    function GetOr(default: R): R
    {
      match this
      case Success(s) => s
      case Failure(e) => default
    }

    /** Converts the Result to an Option */
    function ToOption(): Option<R>
    {
      match this
      case Success(s) => Some(s)
      case Failure(e) => None()
    }

    /** Converts the Result to an Outcome */
    function ToOutcome(): Outcome<E>
    {
      match this
      case Success(s) => Pass
      case Failure(e) => Fail(e)
    }

    /** Applies the given function to convert the Result to something else */
    function Map<FC>(rewrap: Result<R,E> -> FC): FC
    {
      rewrap(this)
    }

    /** Applies the given function to convert the Result to something else with the same Success type */
    function MapFailure<NewE>(reWrap: E -> NewE): Result<R, NewE>
    {
      match this
      case Success(s) => Success(s)
      case Failure(e) => Failure(reWrap(e))
    }
  }

  /** A Pass/Fail failure-compatible datatype that carries an error value, but is not 'value-carrying' */
  datatype Outcome<+E> = Pass | Fail(error: E) {

    predicate IsFailure() {
      Fail?
    }


    function PropagateFailure(): Outcome<E>
      requires Fail?
    {
      this
    }
    // Note: no Extract method, intentionally

    /** Converts to an Option */
    function ToOption<R>(r: R): Option<R>
    {
      match this
      case Pass => Some(r)
      case Fail(e) => None()
    }

    /** Converts to a Result */
    function ToResult<R>(r: R): Result<R,E>
    {
      match this
      case Pass => Success(r)
      case Fail(e) => Failure(e)
    }

    /** Applies the given function to convert to something else */
    function Map<FC>(rewrap: Outcome<E> -> FC): FC
    {
      rewrap(this)
    }

    /** Converts to a Result with a different error type */
    function MapFailure<T,NewE>(rewrap: E-> NewE, default: T): Result<T, NewE>
    {
      match this
      case Pass => Success(default)
      case Fail(e) => Failure(rewrap(e))
    }

    /** A helper function to ensure a requirement is true at runtime,
       returning an Outcome<>. Example:
      `:- Need(5 == |mySet|, "The set MUST have 5 elements.")`
    */
    static function Need(condition: bool, error: E): (result: Outcome<E>)
    {
      if condition then Pass else Fail(error)
    }
  }

  // A special case of Outcome that is just used for Need below, and
  // returns a Result<>
  datatype OutcomeResult<+E> = Pass' | Fail'(error: E) {
    predicate IsFailure() {
      Fail'?
    }
    function PropagateFailure<U>(): Result<U,E>
      requires IsFailure()
    {
      Failure(this.error)
    }
  }

  /** A helper function to ensure a requirement is true at runtime.
      Example: `:- Need(5 == |mySet|, "The set MUST have 5 elements.")`
  */
  function Need<E>(condition: bool, error: E): (result: OutcomeResult<E>)
  {
    if condition then Pass' else Fail'(error)
  }
}
