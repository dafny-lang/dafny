/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
Contains utility functions for date validation, day calculations, and formatting helpers.
*/

module Std.DateTimeUtils {
  import opened Strings
  import opened BoundedInts
  import opened DateTimeConstant
  import opened Wrappers

  const MONTH_NAMES: seq<string> := ["January", "February", "March", "April", "May", "June",
                                     "July", "August", "September", "October", "November", "December"]

  function {:extern "DateTimeImpl.__default", "INTERNAL__ToEpochTimeMilliseconds"}
    {:axiom} INTERNAL__ToEpochTimeMilliseconds(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16): (bool, int, string)

  function ToEpochTimeMilliseconds(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16): Result<int, string>
  {
    var (isError, epochMilliseconds, errorMsg) := INTERNAL__ToEpochTimeMilliseconds(year, month, day, hour, minute, second, millisecond);
    if isError then
      Failure(errorMsg)
    else
      Success(epochMilliseconds)
  }

  function {:extern "DateTimeImpl.__default", "FromEpochTimeMilliseconds"}
    {:axiom} FromEpochTimeMillisecondsFunc(epochMillis: int): seq<int32>
    ensures |FromEpochTimeMillisecondsFunc(epochMillis)| == 7
    ensures var components := FromEpochTimeMillisecondsFunc(epochMillis);
            IsValidDateTime(components[0], components[1] as uint8, components[2] as uint8, components[3] as uint8, components[4] as uint8, components[5] as uint8, components[6] as uint16)

  // External method for getting current time components
  method {:extern "DateTimeImpl.__default", "GetNowComponents"}
    {:axiom} GetNowComponents() returns (components: seq<int32>)
    ensures |components| == 7

  // Leap year calculation using extern implementation
  function {:extern "DateTimeImpl.__default", "IsLeapYear"}
    {:axiom} IsLeapYear(year: int32): bool

  // Days in month calculation
  function DaysInMonth(year: int32, month: uint8): uint8
    requires 1 <= month <= MONTHS_PER_YEAR
  {
    if month == 2 then
      if IsLeapYear(year) then 29 else 28
    else if month == 4 || month == 6 || month == 9 || month == 11 then 30
    else 31
  }

  // Days in year calculation
  function DaysInYear(year: int32): int
  {
    if IsLeapYear(year) then 366 else 365
  }

  // Month name getter
  function GetMonthName(month: uint8): string
    requires 1 <= month <= MONTHS_PER_YEAR
  {
    MONTH_NAMES[month - 1]
  }

  // Date-time validation predicate
  predicate IsValidDateTime(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16)
  {
    MIN_YEAR <= year <= MAX_YEAR &&
    1 <= month <= MONTHS_PER_YEAR &&
    1 <= day <= MAX_DAYS_PER_MONTH &&
    0 <= hour < HOURS_PER_DAY &&
    0 <= minute < MINUTES_PER_HOUR &&
    // Support leap second feature
    0 <= second <= SECONDS_PER_MINUTE &&
    0 <= millisecond < MILLISECONDS_PER_SECOND
  }

  // Helper function for padding numbers with zeros
  function PadWithZeros(value: int, width: int): string
    requires value >= 0
  {
    var valueStr := OfInt(value);
    if |valueStr| >= width then valueStr
    else
      var zerosNeeded := width - |valueStr|;
      var zeros := seq(zerosNeeded, i => '0');
      zeros + valueStr
  }

  // Generate detailed error messages for validation failures
  function GetValidationError(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16): string
  {
    if month < 1 || month > MONTHS_PER_YEAR then "Invalid month: " + OfInt(month as int) + " (must be 1-12)"
    else if day < 1 || day > (DaysInMonth(year, month) as uint8) then "Invalid day: " + OfInt(day as int) + " for " + GetMonthName(month) + " " + OfInt(year as int) + " (max: " + OfInt(DaysInMonth(year, month) as int) + ")"
    else if hour >= HOURS_PER_DAY then "Invalid hour: " + OfInt(hour as int) + " (must be 0-23)"
    else if minute >= MINUTES_PER_HOUR then "Invalid minute: " + OfInt(minute as int) + " (must be 0-59)"
    else if second > SECONDS_PER_MINUTE then "Invalid second: " + OfInt(second as int) + " (must be 0-60)"
    else if millisecond >= MILLISECONDS_PER_SECOND then "Invalid millisecond: " + OfInt(millisecond as int) + " (must be 0-999)"
    else "Invalid date/time"
  }

  // Clamp day to valid range when changing year or month
  function ClampDay(year: int32, month: uint8, desiredDay: uint8): uint8
    requires 1 <= month <= MONTHS_PER_YEAR
    requires desiredDay >= 1
    ensures 1 <= ClampDay(year, month, desiredDay) <= DaysInMonth(year, month)
    ensures desiredDay <= DaysInMonth(year, month) ==> ClampDay(year, month, desiredDay) == desiredDay
    ensures desiredDay >  DaysInMonth(year, month) ==> ClampDay(year, month, desiredDay) == DaysInMonth(year, month)
  {
    if desiredDay <= DaysInMonth(year, month) then desiredDay else DaysInMonth(year, month) as uint8
  }
}