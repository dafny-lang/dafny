/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// This file excludes ORDINAL type from Rust compilation since it's not supported
// in the Rust backend yet.

module {:extern} Std.OrdinalExclusion {
  // Exclude ORDINAL type from Rust compilation
  type {:compile false} BigOrdinal = int
}
