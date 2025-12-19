/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**   
Contains the full implementation of LocalDateTime operations, including creation, parsing,
formatting, arithmetic, and comparison functions.

It defines all verification contracts and imports external DateTime utilities. Uses
epoch-time-based calculations for reliable date arithmetic.
*/

module Std.LocalDateTime {
  import opened Strings
  import opened Wrappers
  import opened BoundedInts
  import opened DateTimeConstant
  import Duration
  import DTUtils = DateTimeUtils

  // Supported date format patterns
  datatype DateFormat =
    | ISO8601                    // yyyy-MM-ddTHH:mm:ss.fff
    | DateOnly                   // yyyy-MM-dd
    | TimeOnly                   // HH:mm:ss
    | DateTimeSpace              // yyyy-MM-dd HH:mm:ss
    | DateSlashDDMMYYYY          // dd/MM/yyyy
    | DateSlashMMDDYYYY          // MM/dd/yyyy

  datatype ParseFormat =
    | ISO8601       // yyyy-MM-ddTHH:mm:ss.fff
    | DateOnly      // yyyy-MM-dd

  // LocalDateTime: represents date-time without time zone information
  datatype LocalDateTime = LocalDateTime(
    year: int32,
    month: uint8,
    day: uint8,
    hour: uint8,
    minute: uint8,
    second: uint8,
    millisecond: uint16
  )

  // LocalDateTime validation predicate
  predicate IsValidLocalDateTime(dt: LocalDateTime)
  {
    DTUtils.IsValidDateTime(dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second, dt.millisecond)
  }

  // LocalDateTime getter functions (bounded integers for efficient storage)
  function GetYear(dt: LocalDateTime): int32 { dt.year }
  function GetMonth(dt: LocalDateTime): uint8 { dt.month }
  function GetDay(dt: LocalDateTime): uint8 { dt.day }
  function GetHour(dt: LocalDateTime): uint8 { dt.hour }
  function GetMinute(dt: LocalDateTime): uint8 { dt.minute }
  function GetSecond(dt: LocalDateTime): uint8 { dt.second }
  function GetMillisecond(dt: LocalDateTime): uint16 { dt.millisecond }

  // Helper conversion functions for cleaner internal calculations
  function ToIntComponents(dt: LocalDateTime): (int, int, int, int, int, int, int)
  {
    (dt.year as int, dt.month as int, dt.day as int, dt.hour as int, dt.minute as int, dt.second as int, dt.millisecond as int)
  }

  function FromComponents(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16): LocalDateTime
    requires DTUtils.IsValidDateTime(year, month, day, hour, minute, second, millisecond)
  {
    LocalDateTime(year, month, day, hour, minute, second, millisecond)
  }

  predicate IsComponentsInValidRange(year: int, month: int, day: int, hour: int := 0, minute: int := 0, second: int := 0, millisecond: int := 0)
  {
    (MIN_YEAR as int) <= year <= (MAX_YEAR as int) &&
    0 <= month <= 255 &&
    0 <= day <= 255 &&
    0 <= hour <= 255 &&
    0 <= minute <= 255 &&
    0 <= second <= 255 &&
    0 <= millisecond <= 65535
  }

  // Helper predicate for component sequences
  predicate IsValidComponentRange(components: seq<int32>)
    requires |components| == 7
  {
    IsComponentsInValidRange(components[0] as int, components[1] as int, components[2] as int,
                             components[3] as int, components[4] as int, components[5] as int, components[6] as int)
  }

  function FromSequenceComponents(components: seq<int32>): LocalDateTime
    requires |components| == 7
    requires IsValidComponentRange(components)
    requires DTUtils.IsValidDateTime(components[0], components[1] as uint8, components[2] as uint8, components[3] as uint8, components[4] as uint8, components[5] as uint8, components[6] as uint16)
  {
    FromComponents(components[0], components[1] as uint8, components[2] as uint8, components[3] as uint8, components[4] as uint8, components[5] as uint8, components[6] as uint16)
  }

  // Modification functions
  function WithYear(dt: LocalDateTime, newYear: int32): LocalDateTime
    requires IsValidLocalDateTime(dt) && MIN_YEAR <= newYear <= MAX_YEAR
    ensures IsValidLocalDateTime(WithYear(dt, newYear))
  {
    var newDay := DTUtils.ClampDay(newYear, dt.month, dt.day);
    FromComponents(newYear, dt.month, newDay, dt.hour, dt.minute, dt.second, dt.millisecond)
  }

  function WithMonth(dt: LocalDateTime, newMonth: uint8): LocalDateTime
    requires IsValidLocalDateTime(dt) && 1 <= newMonth <= 12
    ensures IsValidLocalDateTime(WithMonth(dt, newMonth))
  {
    var newDay := DTUtils.ClampDay(dt.year, newMonth, dt.day);
    FromComponents(dt.year, newMonth, newDay, dt.hour, dt.minute, dt.second, dt.millisecond)
  }

  function WithDayOfMonth(dt: LocalDateTime, newDay: uint8): LocalDateTime
    requires IsValidLocalDateTime(dt) && 1 <= newDay <= (DTUtils.DaysInMonth(dt.year, dt.month) as uint8)
    ensures IsValidLocalDateTime(WithDayOfMonth(dt, newDay))
  {
    FromComponents(dt.year, dt.month, newDay, dt.hour, dt.minute, dt.second, dt.millisecond)
  }

  function WithHour(dt: LocalDateTime, newHour: uint8): LocalDateTime
    requires IsValidLocalDateTime(dt) && newHour < HOURS_PER_DAY
    ensures IsValidLocalDateTime(WithHour(dt, newHour))
  {
    FromComponents(dt.year, dt.month, dt.day, newHour, dt.minute, dt.second, dt.millisecond)
  }

  function WithMinute(dt: LocalDateTime, newMinute: uint8): LocalDateTime
    requires IsValidLocalDateTime(dt) && newMinute < MINUTES_PER_HOUR
    ensures IsValidLocalDateTime(WithMinute(dt, newMinute))
  {
    FromComponents(dt.year, dt.month, dt.day, dt.hour, newMinute, dt.second, dt.millisecond)
  }

  function WithSecond(dt: LocalDateTime, newSecond: uint8): LocalDateTime
    requires IsValidLocalDateTime(dt) && newSecond <= SECONDS_PER_MINUTE
    ensures IsValidLocalDateTime(WithSecond(dt, newSecond))
  {
    FromComponents(dt.year, dt.month, dt.day, dt.hour, dt.minute, newSecond, dt.millisecond)
  }

  function WithMillisecond(dt: LocalDateTime, newMillisecond: uint16): LocalDateTime
    requires IsValidLocalDateTime(dt) && newMillisecond < MILLISECONDS_PER_SECOND
    ensures IsValidLocalDateTime(WithMillisecond(dt, newMillisecond))
  {
    FromComponents(dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second, newMillisecond)
  }

  // Plus methods
  // Epoch-based date time arithmetic
  function Plus(dt: LocalDateTime, millisToAdd: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    var epochMillisResult := DTUtils.ToEpochTimeMilliseconds(dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second, dt.millisecond);
    if epochMillisResult.Failure? then
      Failure(epochMillisResult.error)
    else
      var newEpochMillis := epochMillisResult.value + millisToAdd;
      var components := DTUtils.FromEpochTimeMillisecondsFunc(newEpochMillis);
      if IsValidComponentRange(components) && DTUtils.IsValidDateTime(components[0], components[1] as uint8, components[2] as uint8, components[3] as uint8, components[4] as uint8, components[5] as uint8, components[6] as uint16) then
        Success(FromSequenceComponents(components))
      else
        Failure("Result date/time is out of valid range")
  }

  function PlusDays(dt: LocalDateTime, days: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    Plus(dt, days * (MILLISECONDS_PER_DAY as int))
  }

  function PlusHours(dt: LocalDateTime, hours: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    Plus(dt, hours * (MILLISECONDS_PER_HOUR as int))
  }

  function PlusMinutes(dt: LocalDateTime, minutes: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    Plus(dt, minutes * (MILLISECONDS_PER_MINUTE as int))
  }

  function PlusSeconds(dt: LocalDateTime, seconds: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    Plus(dt, seconds * (MILLISECONDS_PER_SECOND as int))
  }

  function PlusMilliseconds(dt: LocalDateTime, milliseconds: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    Plus(dt, milliseconds)
  }

  function PlusDuration(dt: LocalDateTime, duration: Duration.Duration): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    var totalMillis := (duration.seconds as int) * (MILLISECONDS_PER_SECOND as int) + (duration.millis as int);
    Plus(dt, totalMillis)
  }

  // Minus methods
  function MinusDays(dt: LocalDateTime, days: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    PlusDays(dt, -days)
  }

  function MinusHours(dt: LocalDateTime, hours: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    PlusHours(dt, -hours)
  }

  function MinusMinutes(dt: LocalDateTime, minutes: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    PlusMinutes(dt, -minutes)
  }

  function MinusSeconds(dt: LocalDateTime, seconds: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    PlusSeconds(dt, -seconds)
  }

  function MinusMilliseconds(dt: LocalDateTime, milliseconds: int): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    PlusMilliseconds(dt, -milliseconds)
  }

  function MinusDuration(dt: LocalDateTime, duration: Duration.Duration): Result<LocalDateTime, string>
    requires IsValidLocalDateTime(dt)
  {
    var totalMillis := (duration.seconds as int) * (MILLISECONDS_PER_SECOND as int) + (duration.millis as int);
    Plus(dt, -totalMillis)
  }

  // LocalDateTime comparison function
  function CompareLocal(dt1: LocalDateTime, dt2: LocalDateTime): int
    requires IsValidLocalDateTime(dt1) && IsValidLocalDateTime(dt2)
  {
    if dt1.year != dt2.year then
      if dt1.year < dt2.year then -1 else 1
    else if dt1.month != dt2.month then
      if dt1.month < dt2.month then -1 else 1
    else if dt1.day != dt2.day then
      if dt1.day < dt2.day then -1 else 1
    else if dt1.hour != dt2.hour then
      if dt1.hour < dt2.hour then -1 else 1
    else if dt1.minute != dt2.minute then
      if dt1.minute < dt2.minute then -1 else 1
    else if dt1.second != dt2.second then
      if dt1.second < dt2.second then -1 else 1
    else if dt1.millisecond != dt2.millisecond then
      if dt1.millisecond < dt2.millisecond then -1 else 1
    else
      0
  }

  // Convenience comparison methods
  predicate IsBefore(dt1: LocalDateTime, dt2: LocalDateTime)
    requires IsValidLocalDateTime(dt1) && IsValidLocalDateTime(dt2)
  {
    CompareLocal(dt1, dt2) < 0
  }

  predicate IsAfter(dt1: LocalDateTime, dt2: LocalDateTime)
    requires IsValidLocalDateTime(dt1) && IsValidLocalDateTime(dt2)
  {
    CompareLocal(dt1, dt2) > 0
  }

  predicate IsEqual(dt1: LocalDateTime, dt2: LocalDateTime)
    requires IsValidLocalDateTime(dt1) && IsValidLocalDateTime(dt2)
  {
    CompareLocal(dt1, dt2) == 0
  }

  // Now method which returns current local date time
  method Now() returns (result: Result<LocalDateTime, string>)
    ensures result.Success? ==> IsValidLocalDateTime(result.value)
  {
    var components := DTUtils.GetNowComponents();
    if |components| == 7 &&
       IsValidComponentRange(components) &&
       DTUtils.IsValidDateTime(components[0], components[1] as uint8, components[2] as uint8, components[3] as uint8, components[4] as uint8, components[5] as uint8, components[6] as uint16) {
      result := Success(FromSequenceComponents(components));
    } else {
      result := Failure("Failed to get current time components");
    }
  }

  // Creation functions
  function Of(year: int32, month: uint8, day: uint8, hour: uint8, minute: uint8, second: uint8, millisecond: uint16): Result<LocalDateTime, string>
  {
    if DTUtils.IsValidDateTime(year, month, day, hour, minute, second, millisecond) then
      Success(FromComponents(year, month, day, hour, minute, second, millisecond))
    else
      Failure(DTUtils.GetValidationError(year, month, day, hour, minute, second, millisecond))
  }

  function Parse(text: string, format: ParseFormat): Result<LocalDateTime, string>
  {
    match format {
      case ISO8601 => ParseISO8601(text)
      case DateOnly => ParseDateOnly(text)
    }
  }

  // Parse ISO 8601 format: YYYY-MM-DDTHH:mm:ss.fff
  function ParseISO8601(text: string): Result<LocalDateTime, string>
  {
    if |text| != 23 then
      Failure("Invalid ISO8601 format: expected length 23, got " + OfInt(|text|))
    else if text[4] != '-' || text[7] != '-' || text[10] != 'T' ||
            text[13] != ':' || text[16] != ':' || text[19] != '.' then
      Failure("Invalid ISO8601 format: expected YYYY-MM-DDTHH:mm:ss.fff")
    else
      var yearStr := text[0..4];
      var monthStr := text[5..7];
      var dayStr := text[8..10];
      var hourStr := text[11..13];
      var minuteStr := text[14..16];
      var secondStr := text[17..19];
      var millisecondStr := text[20..23];

      if !DecimalConversion.IsNumberStr(yearStr, '-') ||
         !DecimalConversion.IsNumberStr(monthStr, '-') ||
         !DecimalConversion.IsNumberStr(dayStr, '-') ||
         !DecimalConversion.IsNumberStr(hourStr, '-') ||
         !DecimalConversion.IsNumberStr(minuteStr, '-') ||
         !DecimalConversion.IsNumberStr(secondStr, '-') ||
         !DecimalConversion.IsNumberStr(millisecondStr, '-') then
        Failure("Invalid ISO8601 format: components are not valid numbers")
      else
        var year := ToInt(yearStr);
        var month := ToInt(monthStr);
        var day := ToInt(dayStr);
        var hour := ToInt(hourStr);
        var minute := ToInt(minuteStr);
        var second := ToInt(secondStr);
        var millisecond := ToInt(millisecondStr);

        if IsComponentsInValidRange(year, month, day, hour, minute, second, millisecond) &&
           DTUtils.IsValidDateTime(year as int32, month as uint8, day as uint8, hour as uint8, minute as uint8, second as uint8, millisecond as uint16) then
          Success(FromComponents(year as int32, month as uint8, day as uint8, hour as uint8, minute as uint8, second as uint8, millisecond as uint16))
        else
          Failure("Invalid date/time values")
  }

  // Parse date only format: YYYY-MM-DD (time defaults to 00:00:00.000)
  function ParseDateOnly(text: string): Result<LocalDateTime, string>
  {
    if |text| != 10 then
      Failure("Invalid DateOnly format: expected length 10, got " + OfInt(|text|))
    else if text[4] != '-' || text[7] != '-' then
      Failure("Invalid DateOnly format: expected YYYY-MM-DD")
    else
      var yearStr := text[0..4];
      var monthStr := text[5..7];
      var dayStr := text[8..10];

      if !DecimalConversion.IsNumberStr(yearStr, '-') ||
         !DecimalConversion.IsNumberStr(monthStr, '-') ||
         !DecimalConversion.IsNumberStr(dayStr, '-') then
        Failure("Invalid DateOnly format: components are not valid numbers")
      else
        var year := ToInt(yearStr);
        var month := ToInt(monthStr);
        var day := ToInt(dayStr);
        if IsComponentsInValidRange(year, month, day) &&
           DTUtils.IsValidDateTime(year as int32, month as uint8, day as uint8, 0, 0, 0, 0) then
          Success(FromComponents(year as int32, month as uint8, day as uint8, 0, 0, 0, 0))
        else
          Failure("Invalid date values")
  }


  // Formatting functions
  // ISO 8601 format
  function ToString(dt: LocalDateTime): string
    requires IsValidLocalDateTime(dt)
  {
    var (year, month, day, hour, minute, second, millisecond) := ToIntComponents(dt);
    OfInt(year) + "-" +
    DTUtils.PadWithZeros(month, 2) + "-" +
    DTUtils.PadWithZeros(day, 2) + "T" +
    DTUtils.PadWithZeros(hour, 2) + ":" +
    DTUtils.PadWithZeros(minute, 2) + ":" +
    DTUtils.PadWithZeros(second, 2) + "." +
    DTUtils.PadWithZeros(millisecond, 3)
  }

  function Format(dt: LocalDateTime, format: DateFormat): string
    requires IsValidLocalDateTime(dt)
  {
    var (year, month, day, hour, minute, second, millisecond) := ToIntComponents(dt);
    match format
    case ISO8601 => ToString(dt)
    case DateOnly => OfInt(year) + "-" + DTUtils.PadWithZeros(month, 2) + "-" + DTUtils.PadWithZeros(day, 2)
    case TimeOnly => DTUtils.PadWithZeros(hour, 2) + ":" + DTUtils.PadWithZeros(minute, 2) + ":" + DTUtils.PadWithZeros(second, 2)
    case DateTimeSpace => OfInt(year) + "-" + DTUtils.PadWithZeros(month, 2) + "-" + DTUtils.PadWithZeros(day, 2) + " " +
    DTUtils.PadWithZeros(hour, 2) + ":" + DTUtils.PadWithZeros(minute, 2) + ":" + DTUtils.PadWithZeros(second, 2)
    case DateSlashDDMMYYYY => DTUtils.PadWithZeros(day, 2) + "/" + DTUtils.PadWithZeros(month, 2) + "/" + OfInt(year)
    case DateSlashMMDDYYYY => DTUtils.PadWithZeros(month, 2) + "/" + DTUtils.PadWithZeros(day, 2) + "/" + OfInt(year)
  }
}