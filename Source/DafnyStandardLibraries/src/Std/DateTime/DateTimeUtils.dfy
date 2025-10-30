include "DateTimeConstant.dfy"

module Std.DateTimeUtils {
  import opened Strings
  import opened BoundedInts
  import opened DateTimeConstant

  // Month names for better error messages
  const MONTH_NAMES: seq<string> := ["January", "February", "March", "April", "May", "June",
                                     "July", "August", "September", "October", "November", "December"]

  // Function versions for use in function contexts
  function {:extern "DateTimeImpl", "ToEpochTimeMilliseconds"}
    {:axiom} ToEpochTimeMillisecondsFunc(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16): int

  function {:extern "DateTimeImpl", "FromEpochTimeMilliseconds"}
    {:axiom} FromEpochTimeMillisecondsFunc(epochMillis: int): seq<int32>
    ensures |FromEpochTimeMillisecondsFunc(epochMillis)| == 7
    ensures var components := FromEpochTimeMillisecondsFunc(epochMillis);
            IsValidDateTime(components[0], components[1] as uint8, components[2] as uint8, components[3] as uint8, components[4] as uint8, components[5] as uint8, components[6] as uint16)

  // External method for getting current time components
  method {:extern "DateTimeImpl", "GetNowComponents"}
    {:axiom} GetNowComponents() returns (components: seq<int32>)
    ensures |components| == 7

  // Leap year calculation using extern implementation
  function {:extern "DateTimeImpl", "IsLeapYear"}
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
    0 <= second < SECONDS_PER_MINUTE &&
    0 <= millisecond < MILLISECONDS_PER_SECOND
  }


  // Day of week calculation using Sakamoto's algorithm
  function GetDayOfWeek(year: int32, month: uint8, day: uint8): int32
    requires 1 <= month <= MONTHS_PER_YEAR && 1 <= day <= DaysInMonth(year, month)
  {
    // Returns 0=Sunday, 1=Monday, ..., 6=Saturday
    var t := [0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4];
    var y := if month < 3 then (year as int) - 1 else (year as int);
    var result := (y + y/4 - y/100 + y/400 + t[month-1] + (day as int)) % 7;
    result as int32
  }

  // Convert time portion to total milliseconds since midnight
  function TimeToMilliseconds(hour: uint8, minute: uint8, second: uint8, millisecond: uint16): int
    requires 0 <= hour < HOURS_PER_DAY && 0 <= minute < MINUTES_PER_HOUR
    requires 0 <= second < SECONDS_PER_MINUTE && 0 <= millisecond < MILLISECONDS_PER_SECOND
    ensures 0 <= TimeToMilliseconds(hour, minute, second, millisecond) < (MILLISECONDS_PER_DAY as int)
  {
    (((hour as int) * (MINUTES_PER_HOUR as int) + (minute as int)) * (SECONDS_PER_MINUTE as int) + (second as int)) * (MILLISECONDS_PER_SECOND as int) + (millisecond as int)
  }

  // Convert total milliseconds back to time components
  function MillisecondsToTime(millis: int): (uint8, uint8, uint8, uint16)
    requires 0 <= millis < (MILLISECONDS_PER_DAY as int)
    ensures var (h, m, s, ms) := MillisecondsToTime(millis);
            0 <= h < HOURS_PER_DAY && 0 <= m < MINUTES_PER_HOUR &&
            0 <= s < SECONDS_PER_MINUTE && 0 <= ms < MILLISECONDS_PER_SECOND
  {
    var totalSeconds := millis / (MILLISECONDS_PER_SECOND as int);
    var ms := millis % (MILLISECONDS_PER_SECOND as int);
    var totalMinutes := totalSeconds / (SECONDS_PER_MINUTE as int);
    var s := totalSeconds % (SECONDS_PER_MINUTE as int);
    var h := totalMinutes / (MINUTES_PER_HOUR as int);
    var m := totalMinutes % (MINUTES_PER_HOUR as int);
    (h as uint8, m as uint8, s as uint8, ms as uint16)
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
    else if second >= SECONDS_PER_MINUTE then "Invalid second: " + OfInt(second as int) + " (must be 0-59)"
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