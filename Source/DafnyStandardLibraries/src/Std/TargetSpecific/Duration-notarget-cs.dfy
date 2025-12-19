/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**   
Contains the full implementation of Duration operations, including creation, parsing,
formatting, arithmetic, and comparison functions.

It defines all verification contracts and imports external DateTime Constant. Uses
milliseconds-based calculations for reliable date arithmetic.
*/

module Std.Duration {
  import opened DateTimeConstant
  import opened Strings
  import opened Collections.Seq
  import opened BoundedInts
  import opened Arithmetic.Power
  import opened Wrappers

  datatype Duration = Duration(
    seconds: int,
    millis: int
  )

  function ToTotalMilliseconds(d: Duration): int
  {
    var total: int :=
      (d.seconds * MILLISECONDS_PER_SECOND_INT) +
      d.millis;
    total
  }

  function FromMilliseconds(ms: int): Duration
  {
    var secondsValue := ms / MILLISECONDS_PER_SECOND_INT;
    var millisValue := ms % MILLISECONDS_PER_SECOND_INT;
    Duration(secondsValue, millisValue)
  }

  function Compare(d1: Duration, d2: Duration): int
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    if ms1 < ms2 then -1
    else if ms1 > ms2 then 1
    else 0
  }

  function Less(d1: Duration, d2: Duration): bool
  {
    ToTotalMilliseconds(d1) < ToTotalMilliseconds(d2)
  }

  function LessOrEqual(d1: Duration, d2: Duration): bool
  {
    ToTotalMilliseconds(d1) <= ToTotalMilliseconds(d2)
  }

  // Add two durations
  function Plus(d1: Duration, d2: Duration): Duration
    requires d1.seconds < DURATION_SECONDS_BOUND
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    var sum := ms1 + ms2;
    FromMilliseconds(sum)
  }

  function Minus(d1: Duration, d2: Duration): Duration
    requires ToTotalMilliseconds(d1) >= ToTotalMilliseconds(d2)
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    FromMilliseconds((ms1 - ms2))
  }

  // Scale duration by a factor
  @ResourceLimit("1e7")
  function Scale(d: Duration, factor: int): Duration
    requires ToTotalMilliseconds(d) * factor <= DURATION_SECONDS_BOUND
  {
    var ms := ToTotalMilliseconds(d);
    var product := ms * factor ;
    FromMilliseconds(product)
  }

  // Divide duration by a divisor
  @ResourceLimit("1e7")
  function Divide(d: Duration, divisor: int): Duration
    requires divisor > 0
  {
    FromMilliseconds((ToTotalMilliseconds(d)/ divisor))
  }

  // Modulo operation on durations
  @ResourceLimit("1e7")
  function Mod(d1: Duration, d2: Duration): Duration
    requires ToTotalMilliseconds(d2) > 0
  {
    FromMilliseconds((ToTotalMilliseconds(d1) % ToTotalMilliseconds(d2)))
  }

  // Maximum of two durations
  function Max(d1: Duration, d2: Duration): Duration
  {
    if Less(d1, d2) then d2 else d1
  }

  // Minimum of two durations
  function Min(d1: Duration, d2: Duration): Duration
  {
    if Less(d1, d2) then d1 else d2
  }

  function ToTotalSeconds(d: Duration): int
  {
    d.seconds + (d.millis / (MILLISECONDS_PER_SECOND as int) )
  }

  function ToTotalMinutes(d: Duration): int
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_SECOND as int)
  }

  function ToTotalHours(d: Duration): int
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_SECOND as int)
  }

  function ToTotalDays(d: Duration): int
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_SECOND as int)
  }

  function ConvertToUnit(d: Duration, unitMs: int): int
    requires unitMs > 0
  {
    ToTotalMilliseconds(d) / unitMs
  }

  function FromSeconds(s: int): Duration
  {
    var product := s * (MILLISECONDS_PER_SECOND as int);
    FromMilliseconds(product)
  }

  function FromMinutes(m: int): Duration
  {
    var product := m * (MILLISECONDS_PER_MINUTE as int);
    FromMilliseconds(product)
  }

  function FromHours(h: int): Duration
  {
    var product := h * (MILLISECONDS_PER_MINUTE as int);
    FromMilliseconds(product)
  }

  function FromDays(d: int): Duration
  {
    var product := d * (MILLISECONDS_PER_MINUTE as int);
    FromMilliseconds(product)
  }

  function GetSeconds(d: Duration): int { d.seconds }

  function GetMilliseconds(d: Duration): int { d.millis }

  function ToString(d: Duration): string
  {
    var total_seconds := d.seconds;
    var hours := (total_seconds / (SECONDS_PER_HOUR as int)) as int;
    var minutes := ((total_seconds % (SECONDS_PER_HOUR as int)) / (SECONDS_PER_MINUTE as int)) as int;
    var seconds := (total_seconds % (SECONDS_PER_MINUTE as int)) as int;
    "PT" + OfInt(hours) + "H" + OfInt(minutes) + "M" + OfInt(seconds) + "." +
    OfInt(d.millis as int) + "S"
  }

  function FindCharOrNeg(text: string, ch: char): int
  {
    match IndexOfOption(text, ch)
    case Some(i) => i as int
    case None => -1
  }

  function IsNumeric(s: string): bool
  {
    if |s| == 0 then false
    else forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
  }

  lemma IsNumericSubstring(s: string, start: int, end: int)
    requires IsNumeric(s)
    requires 0 <= start < end <= |s|
    ensures IsNumeric(s[start..end])
  {
  }

  @ResourceLimit("1e7")
  function ParseNumericString(s: string): Result<int, string>
    requires IsNumeric(s)
    decreases |s|
  {
    if |s| == 0 then
      Success(0)
    else if |s| == 1 then
      var digit := (s[0] as int) - ('0' as int);
      Success(digit)
    else
      var digit := (s[0] as int) - ('0' as int);
      IsNumericSubstring(s, 1, |s|);
      match ParseNumericString(s[1..])
      case Success(restValue) =>
        var pow := Pow(10, |s| - 1);
        var result := digit * pow + restValue;
        Success(result)
      case Failure(err) =>
        Failure(err)
  }

  @ResourceLimit("1e7")
  function ParseComponent(text: string, start: int, end: int): Result<int, string>
    requires start >= 0 && end >= 0 && start <= end && end <= |text|
  {
    if start >= end then
      Success(0)
    else
      var substr := text[start..end];
      if IsNumeric(substr) then
        match ParseNumericString(substr)
        case Success(parsed) =>
          if parsed <= DURATION_SECONDS_BOUND then
            Success(parsed as int)
          else
            Failure("Parsed value exceeds maximum uint32")
        case Failure(err) =>
          Failure(err)
      else
        Failure("Non-numeric characters in component")
  }

  @ResourceLimit("1e7")
  function ParseString(text: string): Result<Duration, string>
    requires |text| >= 2
    requires text[0..2] == "PT"
  {
    var len := |text|;

    var hPos := FindCharOrNeg(text, 'H');
    var mPos := FindCharOrNeg(text, 'M');
    var sPos := FindCharOrNeg(text, 'S');
    var dotPos := FindCharOrNeg(text, '.');

    var hourResult :=
      if hPos > 2 then ParseComponent(text, 2, hPos) else Success(0);

    match hourResult
    case Failure(err) => Failure(err)
    case Success(hour) =>

      var minuteStart : int := if hPos > 0 then hPos + 1 else 2;
      var minuteResult :=
        if mPos > minuteStart then ParseComponent(text, minuteStart, mPos) else Success(0);

      match minuteResult
      case Failure(err) => Failure(err)
      case Success(minute) =>

        var secondStart : int := if mPos > 0 then mPos + 1 else 2;
        var secondEnd : int :=
          if dotPos > secondStart then dotPos
          else if sPos > secondStart then sPos
          else len;
        var secondResult :=
          if secondEnd > secondStart then ParseComponent(text, secondStart, secondEnd) else Success(0);

        match secondResult
        case Failure(err) => Failure(err)
        case Success(second) =>

          var millisecondResult :=
            if dotPos > 0 && sPos > dotPos then
              ParseComponent(text, dotPos + 1, sPos)
            else
              Success(0);

          match millisecondResult
          case Failure(err) => Failure(err)
          case Success(raw) =>
            var millisecond : int := if raw < MILLISECONDS_PER_SECOND_INT then (raw as int) else 999;

            var hour_mult := (hour as int) * (SECONDS_PER_HOUR as int);
            var minute_mult := (minute as int) * (SECONDS_PER_MINUTE as int);
            var totalSeconds_val := hour_mult + minute_mult + (second as int);

            if totalSeconds_val <= (DURATION_TOTAL_SECONDS_OUTER_BOUND as int) then
              Success(Duration(totalSeconds_val, millisecond))
            else
              Failure("Total seconds exceeds maximum uint64")
  }

  function EpochDifference(epoch1: int, epoch2: int): Duration
  {
    var diff : int := if epoch1 >= epoch2 then (epoch1 - epoch2) as int
                      else (epoch2 - epoch1) as int;
    FromMilliseconds(diff)
  }
}