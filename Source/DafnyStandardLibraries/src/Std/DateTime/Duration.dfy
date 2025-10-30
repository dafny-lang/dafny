


include "DateTimeConstant.dfy"

module Duration {
  import opened DateTimeConstant
  import opened Std.Strings
  import opened Std.Collections.Seq
  import opened Std.BoundedInts

  datatype Duration = Duration(
    seconds: uint32,
    millis: uint32
  ) {

    ghost predicate Valid() {
      millis < (MILLISECONDS_PER_SECOND as uint32)
    }
  }

  function ToTotalMilliseconds(d: Duration): uint32
    requires d.Valid()
  {

    var product := (d.seconds as uint64) * (MILLISECONDS_PER_SECOND as uint64);
    var sum := product + (d.millis as uint64);
    if sum > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else sum as uint32
  }

  
  function FromMilliseconds(ms: uint32): Duration
    ensures FromMilliseconds(ms).Valid()
  {
    Duration(ms / (MILLISECONDS_PER_SECOND as uint32),
             ms % (MILLISECONDS_PER_SECOND as uint32))
  }



  /// Compare two durations: returns -1 (less), 0 (equal), 1 (greater)
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

  /// Add two durations
  function Plus(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Plus(d1, d2).Valid()
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    var sum := (ms1 as uint64) + (ms2 as uint64);
    var result_ms := if sum > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else sum as uint32;
    FromMilliseconds(result_ms)
  }

  function Minus(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Minus(d1, d2).Valid()
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    FromMilliseconds(ms1 - ms2)
    /** 
    if ms1 >= ms2 then
      FromMilliseconds(ms1 - ms2)
    else
      Duration(0, 0)*/
  }

  /// Scale duration by a factor
  function Scale(d: Duration, factor: uint32): Duration
    requires d.Valid() && factor >= 0
    ensures Scale(d, factor).Valid()
  {
    var ms := ToTotalMilliseconds(d);
    var product := (ms as uint64) * (factor as uint64);
    var result_ms := if product > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else product as uint32;
    FromMilliseconds(result_ms)
  }

  /// Divide duration by a divisor
  function Divide(d: Duration, divisor: uint32): Duration
    requires d.Valid() && divisor > 0
    ensures Divide(d, divisor).Valid()
  {
    FromMilliseconds(ToTotalMilliseconds(d) / divisor)
  }

  /// Modulo operation on durations
  function Mod(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid() && ToTotalMilliseconds(d2) > 0
    ensures Mod(d1, d2).Valid()
  {
    FromMilliseconds(ToTotalMilliseconds(d1) % ToTotalMilliseconds(d2))
  }


  /// Maximum of two durations
  function Max(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Max(d1, d2).Valid()
  {
    if Less(d1, d2) then d2 else d1
  }

  /// Minimum of two durations
  function Min(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Min(d1, d2).Valid()
  {
    if Less(d1, d2) then d1 else d2
  }


  function MaxSeqHelper(durs: seq<Duration>, idx: nat, current: Duration): Duration
    requires forall i :: 0 <= i < |durs| ==> durs[i].Valid()
    requires idx <= |durs|
    requires current.Valid()
    decreases |durs| - idx
    ensures MaxSeqHelper(durs, idx, current).Valid()
  {
    if idx == |durs| then
      current
    else
      var next := if Less(current, durs[idx]) then durs[idx] else current;
      MaxSeqHelper(durs, idx + 1, next)
  }


  function MaxSeq(durs: seq<Duration>): Duration
    requires |durs| > 0
    requires forall i :: 0 <= i < |durs| ==> durs[i].Valid()
    ensures MaxSeq(durs).Valid()
  {
    MaxSeqHelper(durs, 1, durs[0])
  }


  function MinSeqHelper(durs: seq<Duration>, idx: nat, current: Duration): Duration
    requires forall i :: 0 <= i < |durs| ==> durs[i].Valid()
    requires idx <= |durs|
    requires current.Valid()
    decreases |durs| - idx
    ensures MinSeqHelper(durs, idx, current).Valid()
  {
    if idx == |durs| then
      current
    else
      var next := if Less(durs[idx], current) then durs[idx] else current;
      MinSeqHelper(durs, idx + 1, next)
  }


  function MinSeq(durs: seq<Duration>): Duration
    requires |durs| > 0
    requires forall i :: 0 <= i < |durs| ==> durs[i].Valid()
    ensures MinSeq(durs).Valid()
  {
    MinSeqHelper(durs, 1, durs[0])
  }


  function ToTotalSeconds(d: Duration): uint32
    requires d.Valid()
  {
    d.seconds + (d.millis / (MILLISECONDS_PER_SECOND as uint32))
  }

  function ToTotalMinutes(d: Duration): uint32
    requires d.Valid()
  {
    ToTotalMilliseconds(d) / (MILLISECONDS_PER_MINUTE as uint32)
  }

  function ToTotalHours(d: Duration): uint32
    requires d.Valid()
  {
    ToTotalMilliseconds(d) / MILLISECONDS_PER_HOUR
  }

  function ToTotalDays(d: Duration): uint32
    requires d.Valid()
  {
    ToTotalMilliseconds(d) / MILLISECONDS_PER_DAY
  }

  function ConvertToUnit(d: Duration, unitMs: uint32): uint32
    requires d.Valid() && unitMs > 0
  {
    ToTotalMilliseconds(d) / unitMs
  }

  function FromSeconds(s: uint32): Duration
    ensures FromSeconds(s).Valid()
  {
    var product := (s as uint64) * (MILLISECONDS_PER_SECOND as uint64);
    var result_ms := if product > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else product as uint32;
    FromMilliseconds(result_ms)
  }

  function FromMinutes(m: uint32): Duration
    ensures FromMinutes(m).Valid()
  {
    var product := (m as uint64) * (MILLISECONDS_PER_MINUTE as uint64);
    var result_ms := if product > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else product as uint32;
    FromMilliseconds(result_ms)
  }

  function FromHours(h: uint32): Duration
    ensures FromHours(h).Valid()
  {
    var product := (h as uint64) * (MILLISECONDS_PER_HOUR as uint64);
    var result_ms := if product > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else product as uint32;
    FromMilliseconds(result_ms)
  }

  function FromDays(d: uint32): Duration
    ensures FromDays(d).Valid()
  {
    var product := (d as uint64) * (MILLISECONDS_PER_DAY as uint64);
    var result_ms := if product > (OUTER_BOUNDS as uint64) then OUTER_BOUNDS as uint32 else product as uint32;
    FromMilliseconds(result_ms)
  }

  function GetSeconds(d: Duration): uint32 { d.seconds }

  function GetMilliseconds(d: Duration): uint32 { d.millis }

  /// Convert duration to ISO 8601 format: PT[H]H[M]M[S]S.sssS
  function ToString(d: Duration): string
    requires d.Valid()
  {
    var total_seconds := d.seconds;
    var hours := (total_seconds / (SECONDS_PER_HOUR as uint32)) as int;
    var minutes := ((total_seconds % (SECONDS_PER_HOUR as uint32)) / (SECONDS_PER_MINUTE as uint32)) as int;
    var seconds := (total_seconds % (SECONDS_PER_MINUTE as uint32)) as int;
    "PT" + OfInt(hours) + "H" + OfInt(minutes) + "M" + OfInt(seconds) + "." + 
    OfInt(d.millis as int) + "S"
  }

  /// Helper to safely find a character in a string
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

  function ParseNumericString(s: string): nat
    requires forall i :: 0 <= i < |s| ==> s[i] >= '0' && s[i] <= '9'
    decreases |s|
  {
    if |s| == 0 then 0
    else
      var digit := (s[0] as int) - ('0' as int);
      digit * (Pow10(|s| - 1)) + ParseNumericString(s[1..])
  }

  function Pow10(n: nat): nat
    decreases n
  {
    if n == 0 then 1 else 10 * Pow10(n - 1)
  }

  function ParseComponent(text: string, start: int, end: int): uint32
    requires start >= 0 && end >= 0 && start <= end && end <= |text|
  {
    if start >= end then
      0
    else
      var substr := text[start..end];
      if |substr| > 0 && IsNumeric(substr) then 
        var parsed := ParseNumericString(substr);
        if parsed <= OUTER_BOUNDS then parsed as uint32 else OUTER_BOUNDS as uint32
      else 
        0
  }

  function ParseString(text: string): Duration
    requires |text| >= 2
    requires text[0..2] == "PT"
    ensures ParseString(text).Valid()
  {
    var len := |text|;
     
    var hPos := FindCharOrNeg(text, 'H');
    var mPos := FindCharOrNeg(text, 'M');
    var sPos := FindCharOrNeg(text, 'S');
    var dotPos := FindCharOrNeg(text, '.');

    // Extract hour component
    var hour : uint32 := 
      if hPos > 2 then ParseComponent(text, 2, hPos) else 0;

    // Extract minute component
    var minuteStart : int := if hPos > 0 then hPos + 1 else 2;
    var minute : uint32 := 
      if mPos > minuteStart then ParseComponent(text, minuteStart, mPos) else 0;

    // Extract second component
    var secondStart : int := if mPos > 0 then mPos + 1 else 2;
    var secondEnd : int := 
      if dotPos > secondStart then dotPos
      else if sPos > secondStart then sPos
      else len;
    var second : uint32 := 
      if secondEnd > secondStart then ParseComponent(text, secondStart, secondEnd) else 0;

   
    var millisecond : uint32 :=
      if dotPos > 0 && sPos > dotPos then
        var raw := ParseComponent(text, dotPos + 1, sPos);
        if raw < 1000 then raw else 999
      else
        0;

   
    var hour_mult := (hour as uint64) * (SECONDS_PER_HOUR as uint64);
    var minute_mult := (minute as uint64) * (SECONDS_PER_MINUTE as uint64);
    var totalSeconds_val := hour_mult + minute_mult + (second as uint64);
    var totalSeconds := if totalSeconds_val > (OUTER_BOUNDS as uint64) 
                        then OUTER_BOUNDS as uint32 
                        else totalSeconds_val as uint32;
    
    Duration(totalSeconds, millisecond)
  }


  function EpochDifference(epoch1: uint32, epoch2: uint32): Duration
    ensures EpochDifference(epoch1, epoch2).Valid()
  {
    var diff : uint32 := if epoch1 >= epoch2 then (epoch1 - epoch2) as uint32 
                         else (epoch2 - epoch1) as uint32;
    var secs := (diff / 1000 ) as uint32;
    var remMs := (diff % 1000) as uint32;
    Duration(secs, remMs)
  }

}

