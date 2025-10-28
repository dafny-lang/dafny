module DateTimeConstant {
  import opened Std.BoundedInts

  const MILLISECONDS_PER_SECOND: uint16 := 1000
  const SECONDS_PER_MINUTE: uint8 := 60
  const MINUTES_PER_HOUR: uint8 := 60
  const HOURS_PER_DAY: uint8 := 24
  const DURATION_YEAR: uint16 := 9999
  const REGULAR_DAYS_PER_YEAR: uint16 := 365
  
  const MIN_YEAR: int32 := -999999999
  const MAX_YEAR: int32 := 999999999

  // Derived constants for performance
  const MILLISECONDS_PER_MINUTE: uint16 := (SECONDS_PER_MINUTE as uint16) * MILLISECONDS_PER_SECOND
  const MILLISECONDS_PER_HOUR: uint32 := (MINUTES_PER_HOUR as uint32) * (MILLISECONDS_PER_MINUTE as uint32)
  const MILLISECONDS_PER_DAY: uint32 := (HOURS_PER_DAY as uint32) * MILLISECONDS_PER_HOUR
  const MAX_SECONDS_PER_YEAR: uint32 := (SECONDS_PER_MINUTE as uint32) * (MINUTES_PER_HOUR as uint32) * (HOURS_PER_DAY as uint32) * (REGULAR_DAYS_PER_YEAR as uint32) * (DURATION_YEAR as uint32)
  const SECONDS_PER_HOUR: uint16 := (SECONDS_PER_MINUTE as uint16) * (MINUTES_PER_HOUR as uint16)
  const SECONDS_PER_DAY: uint32 := (SECONDS_PER_MINUTE as uint32) * (MINUTES_PER_HOUR as uint32) * (HOURS_PER_DAY as uint32)
}
