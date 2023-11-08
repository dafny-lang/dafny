/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
XXX
*/
module {:options "-functionSyntax:4"} DafnyStdLibs.Math {
  function Min(a: int, b: int): int
  {
    if a < b
    then a
    else
      b
  }

  function Max(a: int, b: int): int
  {
    if a < b
    then b
    else
      a
  }

  function Abs(a: int): (a': int)
    ensures a' >= 0
  {
    if a >= 0 then a else -a
  }
}