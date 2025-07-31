/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// This file excludes ORDINAL-dependent modules from Rust compilation

// Exclude the main Ordinal module
module {:compile false} Std.RsOrdinal replaces Ordinal {}

// Exclude the Termination module which uses ORDINAL
module {:compile false} Std.RsTermination replaces Termination {}
