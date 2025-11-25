/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
Defines time-related constants and bounded integer types used throughout the module.
*/

module Std.DateTimeConstant {
  import opened BoundedInts

  const MILLISECONDS_PER_SECOND: uint16 := 1000
  const SECONDS_PER_MINUTE: uint8 := 60
  const MINUTES_PER_HOUR: uint8 := 60
  const HOURS_PER_DAY: uint8 := 24
  const MONTHS_PER_YEAR: uint8 := 12
  const DURATION_YEAR: uint16 := 9999

  const MIN_YEAR: int32 := -999999999
  const MAX_YEAR: int32 := 999999999
  const MAX_DAYS_PER_MONTH: uint8 := 31

  // Derived constants for performance
  const MILLISECONDS_PER_MINUTE: uint16 := (SECONDS_PER_MINUTE as uint16) * MILLISECONDS_PER_SECOND
  const MILLISECONDS_PER_HOUR: uint32 := (MINUTES_PER_HOUR as uint32) * (MILLISECONDS_PER_MINUTE as uint32)
  const MILLISECONDS_PER_DAY: uint32 := (HOURS_PER_DAY as uint32) * MILLISECONDS_PER_HOUR
  const SECONDS_PER_HOUR: uint16 := (SECONDS_PER_MINUTE as uint16) * (MINUTES_PER_HOUR as uint16)
  const SECONDS_PER_DAY: uint32 := (SECONDS_PER_MINUTE as uint32) * (MINUTES_PER_HOUR as uint32) * (HOURS_PER_DAY as uint32)
}
