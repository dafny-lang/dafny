
 // Optimized Duration Module for Dafny
// Improvements: Better error handling, cleaner logic, no code duplication, performance optimizations

include "DateTimeConstant.dfy"

module Duration {
  import opened DateTimeConstant
  import opened Std.Strings
  import opened Std.Collections.Seq
  import opened Std.BoundedInts

  /// Duration data type representing time with seconds and milliseconds
  datatype Duration = Duration(
    seconds: uint32,
    millis: uint32
  ) {
    // Invariant: millis should be < 1000
    ghost predicate Valid() {
      millis < 1000
    }
  }

  // ============================
  // Core Conversion Functions
  // ============================

  /// Convert duration to total milliseconds
  function ToTotalMilliseconds(d: Duration): uint32
    requires d.Valid()
  {
    (d.seconds as uint32) * (MILLISECONDS_PER_SECOND as uint32) + d.millis
  }

  /// Create duration from milliseconds
  function FromMilliseconds(ms: uint32): Duration
    ensures FromMilliseconds(ms).Valid()
  {
    Duration(ms / (MILLISECONDS_PER_SECOND as uint32),
             ms % (MILLISECONDS_PER_SECOND as uint32))
  }

  // ============================
  // Comparison Operations
  // ============================

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

  /// Check if d1 is strictly less than d2
  function Less(d1: Duration, d2: Duration): bool
    requires d1.Valid() && d2.Valid()
  {
    ToTotalMilliseconds(d1) < ToTotalMilliseconds(d2)
  }

  /// Check if d1 is less than or equal to d2
  function LessOrEqual(d1: Duration, d2: Duration): bool
    requires d1.Valid() && d2.Valid()
  {
    ToTotalMilliseconds(d1) <= ToTotalMilliseconds(d2)
  }

  // ============================
  // Arithmetic Operations
  // ============================

  /// Add two durations
  function Plus(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Plus(d1, d2).Valid()
  {
    FromMilliseconds(ToTotalMilliseconds(d1) + ToTotalMilliseconds(d2))
  }

  /// Subtract d2 from d1 (returns 0 if d2 > d1)
  function Minus(d1: Duration, d2: Duration): Duration
    requires d1.Valid() && d2.Valid()
    ensures Minus(d1, d2).Valid()
  {
    var ms1 := ToTotalMilliseconds(d1);
    var ms2 := ToTotalMilliseconds(d2);
    if ms1 >= ms2 then
      FromMilliseconds(ms1 - ms2)
    else
      Duration(0, 0)
  }

  /// Scale duration by a factor
  function Scale(d: Duration, factor: uint32): Duration
    requires d.Valid() && factor >= 0
    ensures Scale(d, factor).Valid()
  {
    FromMilliseconds(ToTotalMilliseconds(d) * factor)
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

  // ============================
  // Min/Max Operations
  // ============================

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

  /// Helper function for computing max of a sequence
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

  /// Maximum of a non-empty sequence of durations
  function MaxSeq(durs: seq<Duration>): Duration
    requires |durs| > 0
    requires forall i :: 0 <= i < |durs| ==> durs[i].Valid()
    ensures MaxSeq(durs).Valid()
  {
    MaxSeqHelper(durs, 1, durs[0])
  }

  /// Helper function for computing min of a sequence
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

  /// Minimum of a non-empty sequence of durations
  function MinSeq(durs: seq<Duration>): Duration
    requires |durs| > 0
    requires forall i :: 0 <= i < |durs| ==> durs[i].Valid()
    ensures MinSeq(durs).Valid()
  {
    MinSeqHelper(durs, 1, durs[0])
  }

  // ============================
  // Unit Conversion Functions
  // ============================

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

  /// Universal conversion function to avoid code duplication
  function ConvertToUnit(d: Duration, unitMs: uint32): uint32
    requires d.Valid() && unitMs > 0
  {
    ToTotalMilliseconds(d) / unitMs
  }

  function FromSeconds(s: uint32): Duration
    ensures FromSeconds(s).Valid()
  {
    FromMilliseconds(s * (MILLISECONDS_PER_SECOND as uint32))
  }

  function FromMinutes(m: uint32): Duration
    ensures FromMinutes(m).Valid()
  {
    FromMilliseconds(m * (MILLISECONDS_PER_MINUTE as uint32))
  }

  function FromHours(h: uint32): Duration
    ensures FromHours(h).Valid()
  {
    FromMilliseconds(h * MILLISECONDS_PER_HOUR)
  }

  function FromDays(d: uint32): Duration
    ensures FromDays(d).Valid()
  {
    FromMilliseconds(d * MILLISECONDS_PER_DAY)
  }

  // ============================
  // Accessor Functions
  // ============================

  function GetSeconds(d: Duration): uint32 { d.seconds }

  function GetMilliseconds(d: Duration): uint32 { d.millis }

  // ============================
  // String Conversion Functions
  // ============================

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

  /// Helper to safely parse a component from ISO 8601 string
  function ParseComponent(text: string, start: int, end: int): uint32
    requires start >= 0 && end >= 0 && start <= end && end <= |text|
  {
    if start >= end then
      0
    else
      var substr := text[start..end];
      if |substr| > 0 then (ToInt(substr)) as uint32 else 0
  }

  /// Parse ISO 8601 duration string (simplified format support)
  /// Supports: PT[H]H[M]M[S]S.sssS
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

    // Extract millisecond component
    var millisecond : uint32 :=
      if dotPos > 0 && sPos > dotPos then
        ParseComponent(text, dotPos + 1, sPos)
      else
        0;

    // Compute total seconds
    var totalSeconds := hour * (SECONDS_PER_HOUR as uint32) + 
                        minute * (SECONDS_PER_MINUTE as uint32) + 
                        second;
    Duration(totalSeconds, millisecond)
  }

  /// Difference between two epoch times
  
  function EpochDifference(epoch1: uint32, epoch2: uint32): Duration
    ensures EpochDifference(epoch1, epoch2).Valid()
  {
    var diff : uint32 := if epoch1 >= epoch2 then (epoch1 - epoch2) as uint32 
                         else (epoch2 - epoch1) as uint32;
    var secs := (diff / 1000 ) as uint32;
    var remMs := (diff % 1000) as uint32;
    Duration(secs, remMs)
  }

  // ============================
  // Verification Lemmas
  // ============================

  /// Plus operation is associative
  lemma PlusAssociative(d1: Duration, d2: Duration, d3: Duration)
    requires d1.Valid() && d2.Valid() && d3.Valid()
    ensures Plus(Plus(d1, d2), d3) == Plus(d1, Plus(d2, d3))
  {
    // Proof by conversion to milliseconds
  }

  /// Minus is inverse of Plus
  lemma MinusInverse(d1: Duration, d2: Duration)
    requires d1.Valid() && d2.Valid()
    requires ToTotalMilliseconds(d1) >= ToTotalMilliseconds(d2)
    ensures Plus(Minus(d1, d2), d2) == d1
  {
    // Proof by milliseconds arithmetic
  }

  /// Scale is distributive over Plus
  lemma ScaleDistributive(d1: Duration, d2: Duration, factor: uint32)
    requires d1.Valid() && d2.Valid() && factor >= 0
    ensures Scale(Plus(d1, d2), factor) == Plus(Scale(d1, factor), Scale(d2, factor))
  {
    // Proof by multiplication distributivity
  }

  /// Max is commutative
  lemma MaxCommutative(d1: Duration, d2: Duration)
    requires d1.Valid() && d2.Valid()
    ensures Max(d1, d2) == Max(d2, d1)
  {
    if Less(d1, d2) {
      assert !Less(d2, d1);
    } else {
      assert Less(d2, d1) || d1 == d2;
    }
  }
}
