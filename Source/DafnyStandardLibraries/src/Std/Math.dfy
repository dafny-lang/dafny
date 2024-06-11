/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/** Defines various integer-math functions */
module Std.Math {

  /** Minimum of two integers  */
  function Min(a: int, b: int): int
  {
    if a < b
    then a
    else b
  }

  /** Minimum of three integers  */
  function Min3(a: int, b: int, c: int): int
  {
    Min(a, Min(b, c))
  }

  /** Maximum of two integers  */
  function Max(a: int, b: int): int
  {
    if a < b
    then b
    else a
  }

  /** Maximum of three integers  */
  function Max3(a: int, b: int, c: int): int
  {
    Max(a, Max(b, c))
  }

  /** Integer absolute value */
  function Abs(a: int): int
  {
    if a < 0
    then -a
    else a
  }
}
