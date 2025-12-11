/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**   
Contains the full implementation of ZonedDateTime operations, including creation, parsing,
formatting, and arithmetic functions.

It defines all verification contracts and imports external DateTime utilities. Uses
epoch-time-based calculations for reliable date arithmetic.
*/

module Std.ZonedDateTime {
  import opened Strings
  import opened Wrappers
  import opened BoundedInts
  import opened DateTimeConstant
  import LDT = LocalDateTime
  import Duration
  import DTUtils = DateTimeUtils

  // DST status
  // StatusUnique: only one valid offset
  // StatusOverlap: two valid offsets
  // StatusGap: no valid offset, need to shift forward
  // StatusError: error in resolving local date-time
  datatype Status = StatusUnique | StatusOverlap | StatusGap | StatusError

  // Overlap Resolution Preference for resolving local date-time in overlap
  // PreferEarlier: prefer earlier offset in overlap
  // PreferLater: prefer later offset in overlap
  // Error: raise error if overlap occurs
  datatype OverlapResolutionPreference =
    | PreferEarlier
    | PreferLater
    | Error

  // Gap Resolution Preference for resolving local date-time in gap
  // ShiftForward: shift forward to next valid time in gap
  // Error: raise error if gap occurs
  datatype GapResolutionPreference =
    | ShiftForward
    | Error

  datatype ParseFormat =
    | ISO8601       // yyyy-MM-ddTHH:mm:ss.fff±HH:mm or yyyy-MM-ddTHH:mm:ss.fffZ
    | DateOnly      // yyyy-MM-dd±HH:mm or yyyy-MM-ddZ

  datatype DateFormat =
    | ISO8601
    | DateOnly

  // Core structure of ZonedDateTime
  datatype ZonedDateTime = ZonedDateTime(
    local: LDT.LocalDateTime,
    zoneId: string,
    offsetMinutes: int16  // offset in minutes from UTC
  )

  // Invariant: valid local date-time, valid offset (-18h to +18h), zone ID (could be empty)
  predicate IsValidZonedDateTime(zd: ZonedDateTime)
  {
    LDT.IsValidLocalDateTime(zd.local) &&
    MIN_OFFSET_MINUTES <= zd.offsetMinutes <= MAX_OFFSET_MINUTES &&
    0 <= |zd.zoneId|
  }

  // Create a ZonedDateTime from components, resolving local date-time with preference
  function {:extern "ZonedDateTimeImpl.__default", "ResolveLocal"} {:axiom} ResolveLocalImpl(zoneId: string,
                                                                                             year: int32, month: uint8, day: uint8, hour: uint8,
                                                                                             minute: uint8, second: uint8, millisecond: uint16,
                                                                                             overlapPref: OverlapResolutionPreference,
                                                                                             gapPref: GapResolutionPreference) : (result: seq<int32>)
    ensures |result| == 9 && LDT.IsValidComponentRange(result[2..9]) &&
            MIN_OFFSET_MINUTES as int32 <= result[1] <= MAX_OFFSET_MINUTES as int32

  // Helper method to create ZonedDateTime from components
  function {:extern "ZonedDateTimeImpl.__default", "NowZoned"} {:axiom} NowZonedImpl(): seq<int32>
    ensures |NowZonedImpl()| == 8 &&
            LDT.IsValidComponentRange(NowZonedImpl()[1..8]) &&
            MIN_OFFSET_MINUTES as int32 <= NowZonedImpl()[0] <= MAX_OFFSET_MINUTES as int32

  function {:extern "ZonedDateTimeImpl.__default", "GetNowZoneId"} {:axiom} GetNowZoneIdImpl(): seq<char>
    ensures |GetNowZoneIdImpl()| > 0

  // Get current ZonedDateTime
  method Now() returns (result: Result<ZonedDateTime, string>)
    ensures result.Success? ==> IsValidZonedDateTime(result.value)
  {
    var components := NowZonedImpl();
    if |components| == 8 {
      var off := components[0] as int16;
      var year := components[1] as int32;
      var month := components[2] as uint8;
      var day := components[3] as uint8;
      var hour := components[4] as uint8;
      var minute := components[5] as uint8;
      var second := components[6] as uint8;
      var millisecond := components[7] as uint16;
      var local := LDT.LocalDateTime(year, month, day, hour, minute, second, millisecond);

      var zid := GetNowZoneIdImpl();
      var zdt := ZonedDateTime(local, zid, off);
      if IsValidZonedDateTime(zdt) {
        result := Success(zdt);
      } else {
        result := Failure("Invalid ZonedDateTime created");
      }
    } else {
      result := Failure("Failed to get current ZonedDateTime components");
    }
  }

  // Creation function with preference for resolving local date-time
  function Of(zoneId: string, local: LDT.LocalDateTime,
              overlapPreference: OverlapResolutionPreference := OverlapResolutionPreference.Error, gapPreference: GapResolutionPreference := GapResolutionPreference.Error):
    (Result<ZonedDateTime, string>, Status)
    requires LDT.IsValidLocalDateTime(local)
  {
    var p := ResolveLocalImpl(zoneId, local.year, local.month, local.day, local.hour, local.minute, local.second, local.millisecond, overlapPreference, gapPreference);

    var status' :=
      if p[0] as int == 0 then StatusUnique
      else if p[0] as int == 1 then StatusOverlap
      else if p[0] as int == 2 then StatusGap
      else StatusError;

    if status' == StatusError then
      (Failure("Error in resolving local date-time, please specify DST resolution preferences"), status')
    else
      var off := p[1] as int16;
      var ny := p[2] as int32;
      var nm := p[3] as uint8;
      var nd := p[4] as uint8;
      var hh := p[5] as uint8;
      var mm := p[6] as uint8;
      var ss := p[7] as uint8;
      var ms := p[8] as uint16;

      var normLocal := LDT.LocalDateTime(ny, nm, nd, hh, mm, ss, ms);
      var normZoned := ZonedDateTime(normLocal, zoneId, off);
      if IsValidZonedDateTime(normZoned) then
        (Success(normZoned), status')
      else
        (Failure("Normalized local is invalid"), status')
  }

  // ZonedDateTime getter functions (bounded integers for efficient storage)
  function GetYear(dt: ZonedDateTime): int32 { dt.local.year }
  function GetMonth(dt: ZonedDateTime): uint8 { dt.local.month }
  function GetDay(dt: ZonedDateTime): uint8 { dt.local.day }
  function GetHour(dt: ZonedDateTime): uint8 { dt.local.hour }
  function GetMinute(dt: ZonedDateTime): uint8 { dt.local.minute }
  function GetSecond(dt: ZonedDateTime): uint8 { dt.local.second }
  function GetMillisecond(dt: ZonedDateTime): uint16 { dt.local.millisecond }
  function GetLocalDateTime(dt: ZonedDateTime): LDT.LocalDateTime { dt.local }
  function GetZoneId(dt: ZonedDateTime): string { dt.zoneId }
  function GetOffsetMinutes(dt: ZonedDateTime): int16 { dt.offsetMinutes }

  // Modification functions
  function WithYear(dt: ZonedDateTime, newYear: int32): ZonedDateTime
    requires IsValidZonedDateTime(dt) && MIN_YEAR <= newYear <= MAX_YEAR
    ensures IsValidZonedDateTime(WithYear(dt, newYear))
  {
    ZonedDateTime(LDT.WithYear(dt.local, newYear), dt.zoneId, dt.offsetMinutes)
  }

  function WithMonth(dt: ZonedDateTime, newMonth: uint8): ZonedDateTime
    requires IsValidZonedDateTime(dt) && 1 <= newMonth <= MONTHS_PER_YEAR
    ensures IsValidZonedDateTime(WithMonth(dt, newMonth))
  {
    ZonedDateTime(LDT.WithMonth(dt.local, newMonth), dt.zoneId, dt.offsetMinutes)
  }

  function WithDayOfMonth(dt: ZonedDateTime, newDay: uint8): ZonedDateTime
    requires IsValidZonedDateTime(dt) && 1 <= newDay <= DTUtils.DaysInMonth(dt.local.year, dt.local.month)
    ensures IsValidZonedDateTime(WithDayOfMonth(dt, newDay))
  {
    ZonedDateTime(LDT.WithDayOfMonth(dt.local, newDay), dt.zoneId, dt.offsetMinutes)
  }

  function WithHour(dt: ZonedDateTime, newHour: uint8): ZonedDateTime
    requires IsValidZonedDateTime(dt) && newHour < HOURS_PER_DAY
    ensures IsValidZonedDateTime(WithHour(dt, newHour))
  {
    ZonedDateTime(LDT.WithHour(dt.local, newHour), dt.zoneId, dt.offsetMinutes)
  }

  function WithMinute(dt: ZonedDateTime, newMinute: uint8): ZonedDateTime
    requires IsValidZonedDateTime(dt) && newMinute < MINUTES_PER_HOUR
    ensures IsValidZonedDateTime(WithMinute(dt, newMinute))
  {
    ZonedDateTime(LDT.WithMinute(dt.local, newMinute), dt.zoneId, dt.offsetMinutes)
  }

  function WithSecond(dt: ZonedDateTime, newSecond: uint8): ZonedDateTime
    requires IsValidZonedDateTime(dt) && newSecond < SECONDS_PER_MINUTE
    ensures IsValidZonedDateTime(WithSecond(dt, newSecond))
  {
    ZonedDateTime(LDT.WithSecond(dt.local, newSecond), dt.zoneId, dt.offsetMinutes)
  }

  function WithMillisecond(dt: ZonedDateTime, newMillisecond: uint16): ZonedDateTime
    requires IsValidZonedDateTime(dt) && newMillisecond < MILLISECONDS_PER_SECOND
    ensures IsValidZonedDateTime(WithMillisecond(dt, newMillisecond))
  {
    ZonedDateTime(LDT.WithMillisecond(dt.local, newMillisecond), dt.zoneId, dt.offsetMinutes)
  }

  // -- Arithmetic helper functions override for Zoned Date Time --

  function {:extern "DateTimeImpl.__default", "INTERNAL__ToEpochTimeMilliseconds"}
    {:axiom} INTERNAL__ToEpochTimeMilliseconds(year: int32, month: uint8, day: uint8,
                                             hour: uint8, minute: uint8, second: uint8,
                                             millisecond: uint16, offsetMinutes: int16): (bool, int, string)

  function ToEpochTimeMilliseconds(year: int32, month: uint8, day: uint8,
                                   hour: uint8, minute: uint8, second: uint8,
                                   millisecond: uint16, offsetMinutes: int16): Result<int, string>
  {
    var (isError, epochMilliseconds, errorMsg) := INTERNAL__ToEpochTimeMilliseconds(year, month, day,
                                                                                    hour, minute, second,
                                                                                    millisecond, offsetMinutes);
    if isError then
      Failure(errorMsg)
    else
      Success(epochMilliseconds)
  }

  function {:extern "DateTimeImpl.__default", "FromEpochTimeMilliseconds"} {:axiom} FromEpochTimeMillisecondsFunc(epochMillis: int, offsetMinutes: int16): seq<int32>
    ensures |FromEpochTimeMillisecondsFunc(epochMillis, offsetMinutes)| == 7
    ensures var components := FromEpochTimeMillisecondsFunc(epochMillis, offsetMinutes);
            DTUtils.IsValidDateTime(components[0],
                                    components[1] as uint8,
                                    components[2] as uint8,
                                    components[3] as uint8,
                                    components[4] as uint8,
                                    components[5] as uint8,
                                    components[6] as uint16)

  function Plus(dt: ZonedDateTime, millisToAdd: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
    ensures Plus(dt, millisToAdd).Success? ==> IsValidZonedDateTime(Plus(dt, millisToAdd).value)
  {
    var epochMillisResult := ToEpochTimeMilliseconds(dt.local.year, dt.local.month, dt.local.day,
                                                     dt.local.hour, dt.local.minute, dt.local.second,
                                                     dt.local.millisecond, dt.offsetMinutes);
    if epochMillisResult.Failure? then
      Failure(epochMillisResult.error)
    else
      var newEpochMillis := epochMillisResult.value + millisToAdd;
      var components := FromEpochTimeMillisecondsFunc(newEpochMillis, dt.offsetMinutes);
      if LDT.IsValidComponentRange(components) &&
         DTUtils.IsValidDateTime(components[0],
                                 components[1] as uint8,
                                 components[2] as uint8,
                                 components[3] as uint8,
                                 components[4] as uint8,
                                 components[5] as uint8,
                                 components[6] as uint16) then
        Success(ZonedDateTime(LDT.FromSequenceComponents(components), dt.zoneId, dt.offsetMinutes))
      else
        Failure("Result date/time is out of valid range")
  }

  // -- END OF Arithmetic helper functions override for Zoned Date Time --

  // Plus methods
  // Epoch-based date time arithmetic
  function PlusDays(dt: ZonedDateTime, days: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    Plus(dt, days * (MILLISECONDS_PER_DAY as int))
  }

  function PlusHours(dt: ZonedDateTime, hours: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    Plus(dt, hours * (MILLISECONDS_PER_HOUR as int))
  }

  function PlusMinutes(dt: ZonedDateTime, minutes: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    Plus(dt, minutes * (MILLISECONDS_PER_MINUTE as int))
  }

  function PlusSeconds(dt: ZonedDateTime, seconds: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    Plus(dt, seconds * (MILLISECONDS_PER_SECOND as int))
  }

  function PlusMilliseconds(dt: ZonedDateTime, milliseconds: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    Plus(dt, milliseconds)
  }

  function PlusDuration(dt: ZonedDateTime, duration: Duration.Duration): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    var totalMillis := (duration.seconds as int) * (MILLISECONDS_PER_SECOND as int) + (duration.millis as int);
    Plus(dt, totalMillis)
  }

  // Minus methods
  function MinusDays(dt: ZonedDateTime, days: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    PlusDays(dt, -days)
  }

  function MinusHours(dt: ZonedDateTime, hours: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    PlusHours(dt, -hours)
  }

  function MinusMinutes(dt: ZonedDateTime, minutes: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    PlusMinutes(dt, -minutes)
  }

  function MinusSeconds(dt: ZonedDateTime, seconds: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    PlusSeconds(dt, -seconds)
  }

  function MinusMilliseconds(dt: ZonedDateTime, milliseconds: int): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    PlusMilliseconds(dt, -milliseconds)
  }

  function MinusDuration(dt: ZonedDateTime, duration: Duration.Duration): Result<ZonedDateTime, string>
    requires IsValidZonedDateTime(dt)
  {
    var totalMillis := (duration.seconds as int) * (MILLISECONDS_PER_SECOND as int) + (duration.millis as int);
    Plus(dt, -totalMillis)
  }

  // Parsing functions
  function Parse(text: string, format: ParseFormat): Result<ZonedDateTime, string>
  {
    match format {
      case ISO8601 => ParseISO8601(text)
      case DateOnly => ParseDateOnly(text)
    }
  }

  // Helper function to parse offset suffix ±HH:mm or Z
  function ParseOffsetMinutesSuffix(suffix: string): Result<int16, string>
  {
    if |suffix| == 1 then
      if suffix[0] == 'Z'
      then Success(0)
      else Failure("Invalid offset: expected 'Z'")
    else if |suffix| == 6 then
      if !(suffix[0] == '+' || suffix[0] == '-') || suffix[3] != ':' then
        Failure("Invalid offset: expected ±HH:mm")
      else
        var hhStr := suffix[1..3];
        var mmStr := suffix[4..6];

        if !DecimalConversion.IsNumberStr(hhStr, '-') ||
           !DecimalConversion.IsNumberStr(mmStr, '-') then
          Failure("Invalid offset: HH or mm not numeric")
        else
          var hh := ToInt(hhStr);
          var mm := ToInt(mmStr);

          if !(0 <= hh && hh <= 18 && 0 <= mm && mm <= 59 && !(hh == 18 && mm != 0)) then
            Failure("Invalid offset: out of range (must be within ±18:00)")
          else
            var mins := hh * 60 + mm;
            var sign := if suffix[0] == '-' then -1 else 1;
            Success(sign * mins as int16)
    else
      Failure("Invalid offset: expected 'Z' or ±HH:mm")
  }

  // Parse ISO 8601 format: YYYY-MM-DDTHH:mm:ss.fff±HH:mm or YYYY-MM-DDTHH:mm:ss.fffZ
  function ParseISO8601(text: string): Result<ZonedDateTime, string>
  {
    if |text| != 24 && |text| != 29 then
      Failure("Invalid ISO8601Zoned: expected length 24 or 29, got " + OfInt(|text|))
    else
      // Parse the local date-time part
      match LDT.ParseISO8601(text[0..23]) {
        case Failure(msg) => Failure(msg)
        case Success(local) =>
          // Parse the offset part
          match ParseOffsetMinutesSuffix(text[23..|text|]) {
            case Failure(em) => Failure(em)
            case Success(off) => Success(ZonedDateTime(local, "", off))
          }
      }
  }

  // Parse DateOnly format: YYYY-MM-DD±HH:mm or YYYY-MM-DDZ (time defaults to 00:00:00.000)
  function ParseDateOnly(text: string): Result<ZonedDateTime, string>
  {
    if |text| != 11 && |text| != 16 then
      Failure("Invalid DateOnlyZoned format: expected length 11 or 16, got " + OfInt(|text|))
    else
      match LDT.ParseDateOnly(text[0..10]) {
        case Failure(msg) => Failure(msg)
        case Success(local) =>
          match ParseOffsetMinutesSuffix(text[10..|text|]) {
            case Failure(em) => Failure(em)
            case Success(off) => Success(ZonedDateTime(local, "", off))
          }
      }
  }

  // Formatting functions
  // Helper function to format offset suffix ±HH:mm or Z (ISO 8601 style)
  function ToStringSuffix(dt: ZonedDateTime): string
    requires IsValidZonedDateTime(dt)
  {
    if dt.offsetMinutes == 0 then "Z"
    else
      var absOffset := if dt.offsetMinutes < 0 then -dt.offsetMinutes else dt.offsetMinutes;
      var hh := absOffset / 60;
      var mm := absOffset % 60;
      var sign := if dt.offsetMinutes < 0 then "-" else "+";
      sign +
      (if hh < 10 then "0" + OfInt(hh as int) else OfInt(hh as int)) + ":" +
      (if mm < 10 then "0" + OfInt(mm as int) else OfInt(mm as int))
  }

  // Custom date formatting
  function Format(dt: ZonedDateTime, format: DateFormat): string
    requires IsValidZonedDateTime(dt)
  {
    var (year, month, day, hour, minute, second, millisecond) := LDT.ToIntComponents(dt.local);
    match format
    case ISO8601 => LDT.ToString(dt.local) + ToStringSuffix(dt)
    case DateOnly => OfInt(year) + "-" + DTUtils.PadWithZeros(month, 2) + "-" + DTUtils.PadWithZeros(day, 2) + ToStringSuffix(dt)
  }

}