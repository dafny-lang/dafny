module Std.Duration {
  import opened DateTimeConstant
  import opened Strings
  import opened Collections.Seq
  import opened BoundedInts
  import opened Arithmetic.Power
  import opened Wrappers

  datatype Duration = Duration(
    seconds: uint64,
    millis: uint16
  ) {

    ghost predicate Valid() {
      millis < (MILLISECONDS_PER_SECOND as uint16)
    }
  }

  function ToTotalMilliseconds(d: Duration): uint64
    requires d.Valid()
  {
    var product := d.seconds * (MILLISECONDS_PER_SECOND as uint64);
    var sum := product + (d.millis as uint64);
    sum
  }

  function FromMilliseconds(ms: uint32): Duration
    ensures FromMilliseconds(ms).Valid()
  {
    var ms64 := ms as uint64;
    var secondsValue := ms64 / (MILLISECONDS_PER_SECOND as uint64);
    var millisValue := ms64 % (MILLISECONDS_PER_SECOND as uint64);
    var millis := millisValue as uint16;
    Duration(secondsValue, millis)
  }

  // Compare two durations: returns -1 (less), 0 (equal), 1 (greater)
  function Compare(d1: Duration, d2: Duration): int
    requires d1.Valid() && d2.Valid()
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    if ms1 < ms2 then -1
    else if ms1 > ms2 then 1
    else 0
  }

  function Less(d1: Duration, d2: Duration): bool
    requires d1.Valid() && d2.Valid()
  {
    ToTotalMilliseconds(d1) < ToTotalMilliseconds(d2)
  }

  function LessOrEqual(d1: Duration, d2: Duration): bool
    requires d1.Valid() && d2.Valid()
  {
    ToTotalMilliseconds(d1) <= ToTotalMilliseconds(d2)
  }

  // Add two durations
  function Plus(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    requires ToTotalMilliseconds(d1) + ToTotalMilliseconds(d2) <= (0xFFFFFFFF as uint64)
    ensures Plus(d1, d2).Valid()
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    var sum := ms1 + ms2;
    FromMilliseconds(sum as uint32)
  }

  function Minus(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    requires ToTotalMilliseconds(d1) >= ToTotalMilliseconds(d2)
    ensures Minus(d1, d2).Valid()
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    FromMilliseconds((ms1 - ms2) as uint32)
  }
  
  // Scale duration by a factor
  @ResourceLimit("1e7")
  function Scale(d: Duration, factor: uint32): Duration
    requires d.Valid()
    requires ToTotalMilliseconds(d) * (factor as uint64) <= (0xFFFFFFFF as uint64)
    ensures Scale(d, factor).Valid()
  {
    var ms := ToTotalMilliseconds(d);
    var product := ms * (factor as uint64);
    FromMilliseconds(product as uint32)
  }

  // Divide duration by a divisor
  @ResourceLimit("1e7")
  function Divide(d: Duration, divisor: uint32): Duration
    requires d.Valid() && divisor > 0
    ensures Divide(d, divisor).Valid()
  {
    FromMilliseconds((ToTotalMilliseconds(d) / (divisor as uint64)) as uint32)
  }

  // Modulo operation on durations
  @ResourceLimit("1e7")
  function Mod(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid() && ToTotalMilliseconds(d2) > 0
    ensures Mod(d1, d2).Valid()
  {
    FromMilliseconds((ToTotalMilliseconds(d1) % ToTotalMilliseconds(d2)) as uint32)
  }

  // Maximum of two durations
  function Max(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Max(d1, d2).Valid()
  {
    if Less(d1, d2) then d2 else d1
  }

  // Minimum of two durations
  function Min(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Min(d1, d2).Valid()
  {
    if Less(d1, d2) then d1 else d2
  }

  function ToTotalSeconds(d: Duration): uint64
    requires d.Valid()
  {
    d.seconds + ((d.millis as uint64) / (MILLISECONDS_PER_SECOND as uint64))
  }

  function ToTotalMinutes(d: Duration): uint64
    requires d.Valid()
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_MINUTE as uint64)
  }

  function ToTotalHours(d: Duration): uint64
    requires d.Valid()
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_HOUR as uint64)
  }

  function ToTotalDays(d: Duration): uint64
    requires d.Valid()
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_DAY as uint64)
  }

  function ConvertToUnit(d: Duration, unitMs: uint32): uint64
    requires d.Valid() && unitMs > 0
  {
    ToTotalMilliseconds(d) / (unitMs as uint64)
  }

  function FromSeconds(s: uint64): Duration
    requires s * (MILLISECONDS_PER_SECOND as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromSeconds(s).Valid()
  {
    var product := s * (MILLISECONDS_PER_SECOND as uint64);
    FromMilliseconds(product as uint32)
  }

  function FromMinutes(m: uint64): Duration
    requires m * (MILLISECONDS_PER_MINUTE as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromMinutes(m).Valid()
  {
    var product := m * (MILLISECONDS_PER_MINUTE as uint64);
    FromMilliseconds(product as uint32)
  }

  function FromHours(h: uint64): Duration
    requires h * (MILLISECONDS_PER_HOUR as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromHours(h).Valid()
  {
    var product := h * (MILLISECONDS_PER_HOUR as uint64);
    FromMilliseconds(product as uint32)
  }

  function FromDays(d: uint64): Duration
    requires d * (MILLISECONDS_PER_DAY as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromDays(d).Valid()
  {
    var product := d * (MILLISECONDS_PER_DAY as uint64);
    FromMilliseconds(product as uint32)
  }

  function GetSeconds(d: Duration): uint64 { d.seconds }

  function GetMilliseconds(d: Duration): uint16 { d.millis }

  // Convert duration to ISO 8601 format: PT[H]H[M]M[S]S.sssS
  function ToString(d: Duration): string
    requires d.Valid()
  {
    var total_seconds := d.seconds;
    var hours := (total_seconds / (SECONDS_PER_HOUR as uint64)) as int;
    var minutes := ((total_seconds % (SECONDS_PER_HOUR as uint64)) / (SECONDS_PER_MINUTE as uint64)) as int;
    var seconds := (total_seconds % (SECONDS_PER_MINUTE as uint64)) as int;
    "PT" + OfInt(hours) + "H" + OfInt(minutes) + "M" + OfInt(seconds) + "." +
    OfInt(d.millis as int) + "S"
  }

  // Helper to safely find a character in a string
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

  @ResourceLimit("1e7")
  function ParseNumericString(s: string): Result<int, string>
    requires IsNumeric(s)
    decreases |s|
  {
    if |s| == 0 then
      Success(0)
    else
      var digit := (s[0] as int) - ('0' as int);
      match ParseNumericString(s[1..])
      case Success(restValue) =>
        var pow := Pow(10, |s| - 1);
        var result := digit * pow + restValue;
        Success(result)
      case Failure(err) =>
        Failure(err)
  }

  @ResourceLimit("1e7")
  function ParseComponent(text: string, start: int, end: int): Result<uint32, string>
    requires start >= 0 && end >= 0 && start <= end && end <= |text|
  {
    if start >= end then
      Success(0)
    else
      var substr := text[start..end];
      if IsNumeric(substr) then
        match ParseNumericString(substr)
        case Success(parsed) =>
          if parsed <= 0xFFFFFFFF then
            Success(parsed as uint32)
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

    // Extract hour component
    var hourResult :=
      if hPos > 2 then ParseComponent(text, 2, hPos) else Success(0);

    match hourResult
    case Failure(err) => Failure(err)
    case Success(hour) =>

      // Extract minute component
      var minuteStart : int := if hPos > 0 then hPos + 1 else 2;
      var minuteResult :=
        if mPos > minuteStart then ParseComponent(text, minuteStart, mPos) else Success(0);

      match minuteResult
      case Failure(err) => Failure(err)
      case Success(minute) =>

        // Extract second component
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
            var millisecond : uint32 := if raw < 1000 then raw else 999;

            var hour_mult := (hour as uint64) * (SECONDS_PER_HOUR as uint64);
            var minute_mult := (minute as uint64) * (SECONDS_PER_MINUTE as uint64);
            var totalSeconds_val := hour_mult + minute_mult + (second as uint64);

            if totalSeconds_val <= DURATION_TOTAL_SECONDS_OUTER_BOUND then
              Success(Duration(totalSeconds_val, millisecond as uint16))
            else
              Failure("Total seconds exceeds maximum uint64")
  }

  function EpochDifference(epoch1: uint32, epoch2: uint32): Duration
    ensures EpochDifference(epoch1, epoch2).Valid()
  {
    var diff : uint32 := if epoch1 >= epoch2 then (epoch1 - epoch2) as uint32
                         else (epoch2 - epoch1) as uint32;
    FromMilliseconds(diff)
  }
}