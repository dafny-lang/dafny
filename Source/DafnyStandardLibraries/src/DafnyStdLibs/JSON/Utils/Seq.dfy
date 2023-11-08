/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
XXX
*/
module {:options "-functionSyntax:4"} DafnyStdLibs.JSON.Utils.Seq {
  lemma Neutral(l: seq)
    ensures l == l + []
  {}

  lemma Assoc(a: seq, b: seq, c: seq)
    // `a + b + c` is parsed as `(a + b) + c`
    ensures a + b + c == a + (b + c)
  {}


  lemma Assoc'(a: seq, b: seq, c: seq)
    // `a + b + c` is parsed as `(a + b) + c`
    ensures a + (b + c) == a + b + c
  {}

  lemma Assoc2(a: seq, b: seq, c: seq, d: seq)
    // `a + b + c + d` is parsed as `((a + b) + c) + d`
    ensures a + b + c + d == a + (b + c + d)
  {}
}