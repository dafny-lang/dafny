/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
 This module defines useful properties and functions relating to the built-in tuple type.
 */
module Std.Collections.Tuple {
  /** Extracts the first component of a pair */
  function T2_0<L, R>(): ((L, R)) -> L {
    (lr: (L, R)) => lr.0
  }

  /** Extracts the second component of a pair */
  function T2_1<L, R>(): ((L, R)) -> R {
    (lr: (L, R)) => lr.1
  }
}
