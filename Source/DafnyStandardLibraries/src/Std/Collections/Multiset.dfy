/*******************************************************************************
 *  Original Copyright under the following:
 *  Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University,
 *  ETH Zurich, and University of Washington
 *  SPDX-License-Identifier: BSD-2-Clause
 *
 *  Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
 This module defines useful properties and functions relating to the built-in `multiset` type.
 */
module Std.Collections.Multiset {


  /* Non-deterministically extracts an element from a multiset that contains at least one element. */
  ghost function ExtractFromNonEmptyMultiset<T>(s: multiset<T>): (x: T)
    requires |s| != 0
    ensures x in s
  {
    var x :| x in s;
    x
  }

  /* If x is a subset of y, then the size of x is less than or equal to the
  size of y. */
  lemma LemmaSubmultisetSize<T>(x: multiset<T>, y: multiset<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
  {
    if x != multiset{} {
      var e :| e in x;
      LemmaSubmultisetSize(x - multiset{e}, y - multiset{e});
    }
  }
}