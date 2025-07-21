/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// This file provides a workaround for the ORDINAL type in Rust compilation
// since it's not supported in the Rust backend yet.

// Provide a replacement for the Ordinal module for Rust
module {:compile false} Std.RsOrdinal replaces Ordinal {
  // This module is empty and marked as compile:false for Rust
  // This prevents the ORDINAL type from being used in Rust compilation
}
