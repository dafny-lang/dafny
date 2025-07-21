/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// This file excludes modules that use ORDINAL type from Rust compilation

// Mark the Ordinal module as compile:false for Rust
@Compile(false)
module Std.RsOrdinal replaces Ordinal {}

// Mark the Termination module as compile:false for Rust  
@Compile(false)
module Std.RsTermination replaces Termination {}

// Mark all Actions modules as compile:false for Rust
@Compile(false)
module Std.Actions.RsProducers replaces Producers {}

@Compile(false)
module Std.Actions.RsBulkActions replaces BulkActions {}

@Compile(false)
module Std.Actions.RsGenericAction replaces GenericAction {}

@Compile(false)
module Std.Actions.RsActions replaces Actions {}

@Compile(false)
module Std.Actions.RsConsumers replaces Consumers {}
