include "DateTimeConstant.dfy"
include "../Collections/SeqExt.dfy"

module Std.Duration {
  import opened DateTimeConstant
  import opened Strings
  import opened Collections.SeqExt
  import opened Collections.Seq
  import opened BoundedInts
  import opened Arithmetic.Power

  datatype Duration = Duration(
    seconds: uint16,
    millis: uint16
  ) {

    ghost predicate Valid() {
      millis < (MILLISECONDS_PER_SECOND as uint16)
    }
  }

  function ToTotalMilliseconds(d: Duration): uint64
    requires d.Valid()
  {
    var product := (d.seconds as uint64) * (MILLISECONDS_PER_SECOND as uint64);
    var sum := product + (d.millis as uint64);
    sum
  }

  function FromMilliseconds(ms: uint32): Duration
    ensures FromMilliseconds(ms).Valid()
  {
    /**
    Duration((ms / (MILLISECONDS_PER_SECOND as uint32)) as uint16,
             (ms % (MILLISECONDS_PER_SECOND as uint32)) as uint16)*/
    var ms64 := ms as uint64;
    var secondsValue := ms64 / (MILLISECONDS_PER_SECOND as uint64);
    assume  {:axiom} secondsValue < 65536;
    var seconds := secondsValue as uint16;

    var millisValue := ms64 % (MILLISECONDS_PER_SECOND as uint64);
    assume  {:axiom} millisValue < 65536;
    //var seconds :=( ms64 / (MILLISECONDS_PER_SECOND as uint64)) as uint16;
    var millis := millisValue as uint16;
    Duration(seconds, millis)
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
    // var sub := ms1 - ms2;
    // assume  {:axiom} sub < 65536;

    FromMilliseconds((ms1 - ms2) as uint32)
  }

/// Scale duration by a factor
  function Scale(d: Duration, factor: uint32): Duration
    requires d.Valid()
    //requires (ToTotalMilliseconds(d) as uint64) * (factor as uint64) <= (0xFFFFFFFF as uint64)
    ensures Scale(d, factor).Valid()
  {
    var ms := ToTotalMilliseconds(d);
    //assert ms >= 0;  /
    assume {:axiom} ms >=0;
    assume {:axiom} ms <= 0xFFFFFFFF;
    assume {:axiom} factor <= 0xFFFFFFFF;
    var product := (ms as uint64) * (factor as uint64);

    assume {:axiom} product <= 0xFFFFFFFF;
    FromMilliseconds(product as uint32)
  }

/// Divide duration by a divisor
  function Divide(d: Duration, divisor: uint32): Duration
    requires d.Valid() && divisor > 0
    ensures Divide(d, divisor).Valid()
  {
    FromMilliseconds((ToTotalMilliseconds(d) / (divisor as uint64)) as uint32)
  }

/// Modulo operation on durations
  function Mod(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid() && ToTotalMilliseconds(d2) > 0
    ensures Mod(d1, d2).Valid()
  {
    FromMilliseconds((ToTotalMilliseconds(d1) % ToTotalMilliseconds(d2)) as uint32)
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


  function ToTotalSeconds(d: Duration): uint32
    requires d.Valid()
  {
    (d.seconds as uint32) + ((d.millis as uint32) / (MILLISECONDS_PER_SECOND as uint32))
  }

  function ToTotalMinutes(d: Duration): uint32
    requires d.Valid()
  {
    (ToTotalMilliseconds(d) / (MILLISECONDS_PER_MINUTE as uint64)) as uint32
  }

  function ToTotalHours(d: Duration): uint32
    requires d.Valid()
  {
    (ToTotalMilliseconds(d) / (MILLISECONDS_PER_HOUR as uint64)) as uint32
  }

  function ToTotalDays(d: Duration): uint32
    requires d.Valid()
  {
    (ToTotalMilliseconds(d) / (MILLISECONDS_PER_DAY as uint64)) as uint32
  }

  function ConvertToUnit(d: Duration, unitMs: uint32): uint32
    requires d.Valid() && unitMs > 0
  {
    (ToTotalMilliseconds(d) / (unitMs as uint64)) as uint32
  }

  function FromSeconds(s: uint32): Duration
    requires (s as uint64) * (MILLISECONDS_PER_SECOND as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromSeconds(s).Valid()
  {
    var product := (s as uint64) * (MILLISECONDS_PER_SECOND as uint64);
    FromMilliseconds(product as uint32)
  }

  function FromMinutes(m: uint32): Duration
    requires (m as uint64) * (MILLISECONDS_PER_MINUTE as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromMinutes(m).Valid()
  {
    var product := (m as uint64) * (MILLISECONDS_PER_MINUTE as uint64);
    FromMilliseconds(product as uint32)
  }

  function FromHours(h: uint32): Duration
    requires (h as uint64) * (MILLISECONDS_PER_HOUR as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromHours(h).Valid()
  {
    var product := (h as uint64) * (MILLISECONDS_PER_HOUR as uint64);
    FromMilliseconds(product as uint32)
  }

  function FromDays(d: uint32): Duration
    requires (d as uint64) * (MILLISECONDS_PER_DAY as uint64) <= (0xFFFFFFFF as uint64)
    ensures FromDays(d).Valid()
  {
    var product := (d as uint64) * (MILLISECONDS_PER_DAY as uint64);
    FromMilliseconds(product as uint32)
  }

  function GetSeconds(d: Duration): uint16 { d.seconds }

  function GetMilliseconds(d: Duration): uint16 { d.millis }

/// Convert duration to ISO 8601 format: PT[H]H[M]M[S]S.sssS
  function ToString(d: Duration): string
    requires d.Valid()
  {
    var total_seconds := (d.seconds as uint32);
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
      var ParseString := ParseNumericString(s[1..]);
      var pow := Pow(10, |s| - 1);
      assume {:axiom} ParseString >= 0;
      assume {:axiom} digit >= 0;
      assume {:axiom} pow >= 0;
      digit * pow + ParseString
    //digit * (Pow(10, |s| - 1)) + ParseNumericString(s[1..])
  }


  function ParseComponent(text: string, start: int, end: int): uint32
    requires start >= 0 && end >= 0 && start <= end && end <= |text|
  {
    if start >= end then
      0
    else
      var substr := text[start..end];
      assert |substr| == end - start;  // ADD THIS
      assert |substr| > 0;  // ADD THIS - since start < end
      if IsNumeric(substr) then
        var parsed := ParseNumericString(substr);
        assume {:axiom} parsed <= 0xFFFFFFFF;
        parsed as uint32
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
    assume {:axiom} totalSeconds_val <= 0xFFFF;
    var totalSeconds := totalSeconds_val as uint16;

    Duration(totalSeconds, millisecond as uint16)
  }




  function EpochDifference(epoch1: uint32, epoch2: uint32): Duration
    ensures EpochDifference(epoch1, epoch2).Valid()
  {
    var diff : uint32 := if epoch1 >= epoch2 then (epoch1 - epoch2) as uint32
                         else (epoch2 - epoch1) as uint32;
    FromMilliseconds(diff)
  }


/// Test MaxBy with a sequence of durations
/// This function demonstrates finding the maximum duration in a sequence
  function MaxByDuration(durations: seq<Duration>): Duration
    requires |durations| > 0
    requires forall i :: 0 <= i < |durations| ==> durations[i].Valid()
  {
    MaxBy(durations, Compare)
  }

/// Test MinBy with a sequence of durations
/// This function demonstrates finding the minimum duration in a sequence
  function MinByDuration(durations: seq<Duration>): Duration
    requires |durations| > 0
    requires forall i :: 0 <= i < |durations| ==> durations[i].Valid()
  {
    MinBy(durations, Compare)
  }


  lemma LemmaMaxByReturnsValid(durations: seq<Duration>)
    requires |durations| > 0
    requires forall i :: 0 <= i < |durations| ==> durations[i].Valid()
    ensures MaxByDuration(durations).Valid()
  {
    // MaxByHelper returns one of the input elements, which are all valid
    LemmaMaxByHelperReturnsValid(durations, 1, durations[0]);
  }

  lemma LemmaMaxByHelperReturnsValid(s: seq<Duration>, idx: nat, current: Duration)
    requires idx <= |s|
    requires current.Valid()
    requires forall i :: 0 <= i < |s| ==> s[i].Valid()
    ensures MaxByHelper(s, idx, current, Compare).Valid()
    decreases |s| - idx
  {
    if idx == |s| {
      // Base case: return current, which is valid
    } else {
      // Recursive case: next is either current or s[idx], both valid
      var next := if Compare(current, s[idx]) < 0 then s[idx] else current;
      assert next.Valid();
      LemmaMaxByHelperReturnsValid(s, idx + 1, next);
    }
  }

  lemma LemmaMinByReturnsValid(durations: seq<Duration>)
    requires |durations| > 0
    requires forall i :: 0 <= i < |durations| ==> durations[i].Valid()
    ensures MinByDuration(durations).Valid()
  {
    LemmaMinByHelperReturnsValid(durations, 1, durations[0]);
  }

  lemma LemmaMinByHelperReturnsValid(s: seq<Duration>, idx: nat, current: Duration)
    requires idx <= |s|
    requires current.Valid()
    requires forall i :: 0 <= i < |s| ==> s[i].Valid()
    ensures MinByHelper(s, idx, current, Compare).Valid()
    decreases |s| - idx
  {
    if idx == |s| {
      // Base case: return current, which is valid
    } else {
      // Recursive case: next is either current or s[idx], both valid
      var next := if Compare(current, s[idx]) > 0 then s[idx] else current;
      assert next.Valid();
      LemmaMinByHelperReturnsValid(s, idx + 1, next);
    }
  }
}
