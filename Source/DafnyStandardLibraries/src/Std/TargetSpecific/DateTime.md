# LocalDateTime Module Introduction

The `LocalDateTime` module provides formally verified date and time functionality in Dafny without timezone information.  
It ensures correctness using contracts (`requires`, `ensures`) and supports proof-based reasoning for temporal computations.

## File Descriptions

- **`LocalDateTime.dfy`**  
  Core implementation of LocalDateTime operations including creation, parsing, arithmetic, formatting, comparison, and modification.  
  Uses epoch-time conversion for accuracy across month/year boundaries with full verification contracts.

- **`LocalDateTimeExamples.dfy`**  
  Test methods validating all LocalDateTime functionality using Dafny's `{:test}` annotation for formal verification.

- **`DateTimeImpl.cs`**  
  External implementation of system-dependent operations for current time retrieval and epoch-time conversions.

- **`DateTimeConstant.dfy`**  
  Time-related constants and bounded integer types including fundamental values like milliseconds per second, year bounds, and derived performance constants.

- **`DateTimeUtils.dfy`**  
  Utility functions for date validation, leap year calculations, time conversions, and error message generation.

## Function Descriptions

- **Creation Functions**  
  - `Of()`: Creates a LocalDateTime from individual components with validation.
  - `Now()`: Returns the current local date and time.
  - `FromSequenceComponents()`: Creates from a sequence of integer components.

- **Parsing Functions**  
  - `Parse()`: Parses strings in ISO8601 or DateOnly formats.
  - `ParseISO8601()`: Specifically handles "YYYY-MM-DDTHH:mm:ss.fff" format.
  - `ParseDateOnly()`: Handles "YYYY-MM-DD" format with time defaulting to midnight.

- **Arithmetic Operations**  
  - `Plus/Minus` functions for days, hours, minutes, seconds, milliseconds.
  - `PlusDuration()/MinusDuration()`: Add or subtract Duration objects.
  - All operations use epoch-time conversion for accuracy across month/year boundaries.

- **Formatting Functions**  
  - `ToString()`: Default ISO8601 string representation.
  - `Format()`: Supports multiple formats (ISO8601, DateOnly, TimeOnly, etc.).

- **Comparison Functions**  
  - `CompareLocal()`: Returns -1, 0, or 1 for ordering.
  - `IsBefore()`, `IsAfter()`, `IsEqual()`: Boolean comparison predicates.

- **Modification Functions**  
  - `With` functions: Create new instances with modified components (year, month, day, etc.).
  - Automatically handles date clamping (e.g., Feb 29 → Feb 28 in non-leap years).

- **Getter Functions**  
  - Individual component accessors: `GetYear()`, `GetMonth()`, `GetDay()`, etc.
  - `IsValidLocalDateTime()`: Validates a LocalDateTime instance.

# Duration Module Introduction

The `Duration` module provides formally verified operations for representing and manipulating time durations in Dafny.  
It ensures mathematical correctness using contracts (`requires`, `ensures`) and safe overflow handling via bounded integer arithmetic.  
This module underpins temporal computations in the LocalDateTime system by enabling precise duration arithmetic and comparisons.

## File Descriptions

- **`Duration.dfy`**  
  Core Duration datatype implementation with creation, arithmetic, comparison, and conversion functions.  
  Includes proof contracts ensuring validity (millis < 1000) and robust overflow handling using 64-bit intermediate computations.

- **`DurationExamples.dfy`**  
  Test examples validating all Duration operations using Dafny's `{:test}` annotation for formal verification.

## Function Descriptions

- **Datatype Definition**  
  `datatype Duration = Duration(seconds: uint32, millis: uint32)`  
  Represents a duration as a combination of seconds and milliseconds.

- **Creation Functions**  
  - `FromMilliseconds(ms: uint32)`: Converts a millisecond value into a valid Duration, splitting it into seconds and leftover milliseconds.
  - `FromSeconds(s: uint32)`: Creates a Duration equivalent to the given number of seconds.
  - `FromMinutes(m: uint32)`, `FromHours(h: uint32)`, `FromDays(d: uint32)`: Scale minutes, hours, or days into milliseconds and construct a valid duration object.

- **Arithmetic Operations**  
  - `Plus(d1, d2) / Minus(d1, d2)`: Performs addition or subtraction of two durations, clamping results to 32-bit maximums. Minus returns zero duration if the result would be negative.
  - `Scale(d, factor)`: Multiplies a duration by an integer factor, with overflow protection.
  - `Divide(d, divisor)`: Divides a duration by a positive integer, truncating fractional parts.
  - `Mod(d1, d2)`: Computes the remainder of one duration divided by another.

- **Comparison Functions**  
  - `Compare(d1, d2)`: Returns -1, 0, or 1 to indicate whether d1 is less than, equal to, or greater than d2.
  - `Less(d1, d2) / LessOrEqual(d1, d2)`: Boolean predicates for ordering durations.
  - `Max(d1, d2) / Min(d1, d2)`: Returns the greater or lesser of two durations.
  - `MaxSeq(durs) / MinSeq(durs)`: Computes the maximum or minimum duration from a non-empty sequence using recursive helper functions with termination proofs.

- **Conversion Functions**  
  - `ToTotalMilliseconds(d)`: Converts a duration to total milliseconds as a 32-bit integer with overflow handling.
  - `ToTotalSeconds(d), ToTotalMinutes(d), ToTotalHours(d), ToTotalDays(d)`: Converts the duration into progressively larger time units using constant ratios.
  - `ConvertToUnit(d, unitMs)`: Converts a duration into arbitrary units defined by the given millisecond base.

- **Accessors**  
  - `GetSeconds(d), GetMilliseconds(d)`: Returns individual components of the duration.

- **Formatting and Parsing**  
  - `ToString(d)`: Converts a duration into an ISO 8601–compliant string of the form PT#H#M#S.sssS.
  - `ParseString(text)`: Parses a duration string in ISO 8601 format (PT#H#M#S.sssS) into a valid Duration.  
  Includes helper functions for parsing numeric substrings (ParseNumericString, ParseComponent) and locating delimiters (FindCharOrNeg).

- **Internal Helper Functions**  
  - `FindCharOrNeg(text, ch)`: Finds a character or returns -1.
  - `IsNumeric(s)`: Checks if all characters in a string are digits.
  - `Pow10(n)`: Computes 10ⁿ recursively for numeric parsing.

- **Derived Computation**  
  - `EpochDifference(epoch1, epoch2)`: Computes the absolute duration difference between two epoch millisecond timestamps, returning a valid Duration instance.


# A Verified DateTime Library for Dafny

Date and time handling is one of the most error-prone areas in software development.

From leap year calculations to timezone transitions, temporal data presents edge cases that can corrupt application logic. This becomes critical in verification languages like Dafny, where correctness is mathematically proven.

We built `Std.LocalDateTime` and `Std.ZonedDateTime`, comprehensive modules providing timezone-agnostic and timezone-aware date-time operations with full formal verification. This post covers:

* design principles behind safe temporal arithmetic,
* validation and bounded integer types,
* timezone handling and DST resolution,
* parsing and formatting with formal contracts,
* epoch-based arithmetic for reliable calculations,
* verification challenges we solved.


## Design principles

Our design balances mathematical precision with real-world complexity:

1. **Safety through types:** Bounded integer types (`int32`, `uint8`, `uint16`) prevent overflow while maintaining verification guarantees.

2. **Explicit validation:** Every instance must satisfy validity predicates, checking leap years, month boundaries, time constraints, and (for zoned times) offset bounds.

3. **Immutability:** Pure functions like `WithYear`, `WithMonth` return new validated instances instead of mutation.

4. **Epoch-based arithmetic:** Date arithmetic converts to epoch milliseconds, performs calculation, then converts back—avoiding calendar complexity.

5. **Parsing with validation:** Parsing functions return `Result<T, string>`, performing runtime validation checks and forcing explicit error handling.

6. **First-class DST semantics (ZonedDateTime):** Ambiguity is explicit: we model states StatusUnique, StatusOverlap, StatusGap, StatusError and take two preferences (OverlapResolutionPreference & GapResolutionPreference) for resolution. No hidden heuristics.


## The core datatypes and validation

### LocalDateTime: Timezone-agnostic

The `LocalDateTime` datatype represents a calendar date and wall-clock time without timezone information:

<!-- %no-check -->
```dafny
datatype LocalDateTime = LocalDateTime(
  year: int32,
  month: uint8,
  day: uint8,
  hour: uint8,
  minute: uint8,
  second: uint8,
  millisecond: uint16
)

predicate IsValidLocalDateTime(dt: LocalDateTime)
{
  DTUtils.IsValidDateTime(dt.year, dt.month, dt.day,
    dt.hour, dt.minute, dt.second, dt.millisecond)
}
```

This checks month boundaries (1-12), days within each month (including leap years), time ranges (0-23 hours, 0-59 minutes), and supports leap seconds.

### ZonedDateTime: Timezone-aware

The `ZonedDateTime` datatype adds timezone context through a zone identifier and explicit offset:

<!-- %no-check -->
```dafny
datatype ZonedDateTime = ZonedDateTime(
    local: LDT.LocalDateTime,
    zoneId: string,
    offsetMinutes: int16
)

predicate IsValidZonedDateTime(zd: ZonedDateTime)
{
  LDT.IsValidLocalDateTime(zd.local) &&
  MIN_OFFSET_MINUTES <= zd.offsetMinutes <= MAX_OFFSET_MINUTES &&
  0 <= |zd.zoneId|
}

```

We cap offsets at ±18 hours (1080 minutes) to align with practical timezone limits. Every function requires valid input and ensures valid output.


## Construction and DST resolution

### LocalDateTime: Simple construction

LocalDateTime construction validates components and returns a Result:

<!-- %no-check -->
```dafny
function Of(year: int32, month: uint8, day: uint8,
           hour: uint8, minute: uint8, second: uint8,
           millisecond: uint16): Result<LocalDateTime, string>
{
  if DTUtils.IsValidDateTime(year, month, day, hour, minute, second, millisecond) then
    Success(FromComponents(year, month, day, hour, minute, second, millisecond))
  else
    Failure(DTUtils.GetValidationError(year, month, day, hour, minute, second, millisecond))
}
```

### ZonedDateTime: DST-aware construction

ZonedDateTime construction requires DST ambiguity resolution. We represent the outcome explicitly:

<!-- %no-check -->
```dafny
  datatype Status = StatusUnique | StatusOverlap | StatusGap | StatusError

  datatype OverlapResolutionPreference =
    | PreferEarlier
    | PreferLater
    | Error

  datatype GapResolutionPreference =
    | ShiftForward
    | Error
```

The constructor uses a single extern to perform platform-aware resolution:

<!-- %no-check -->
```dafny
function {:extern "ZonedDateTimeImpl.__default", "ResolveLocal"} {:axiom} ResolveLocalImpl(zoneId: string,
                                                                                           year: int32, month: uint8, day: uint8, hour: uint8, 
                                                                                           minute: uint8, second: uint8, millisecond: uint16,
                                                                                           overlapPreferenceIndex: int8, gapPreferenceIndex: int8) : (result: seq<int32>)
    ensures |result| == 9 && LDT.IsValidComponentRange(result[2..9]) && -18*60 <= result[1] <= 18*60
```

We wrap it in a verified `Of` that produces a ZonedDateTime and the Status:

<!-- %no-check -->
```dafny
function Of(zoneId: string, local: LDT.LocalDateTime, 
    overlapPreference: OverlapResolutionPreference := OverlapResolutionPreference.Error, gapPreference: GapResolutionPreference := GapResolutionPreference.Error): 
    (Result<ZonedDateTime, string>, Status)
    requires LDT.IsValidLocalDateTime(local)
  {
    // Calls ResolveLocalImpl and builds a normalized ZonedDateTime
    // Status: 0=Unique, 1=Overlap, 2=Gap, 3=Error
    …
  }
```

### What the preferences mean

On **Overlap** (clocks set back, two valid instants for the same "wall time"):

* `PreferEarlier` picks the earlier UTC instant (the first occurrence),
* `PreferLater` picks the later UTC instant (the second occurrence).
* `Error` raises error if overlap occurs (default)

On **Gap** (clocks jump forward, a "wall time" doesn't exist):

* `ShiftForward` moves forward to the next valid minute.
* `Error` raises error if gap occurs (default)

These rules are implemented once in the extern and reflected in verified postconditions inside Dafny.


## Immutable transformations

### LocalDateTime transformations

<!-- %no-check -->
```dafny
function WithYear(dt: LocalDateTime, newYear: int32): LocalDateTime
  requires IsValidLocalDateTime(dt) && MIN_YEAR <= newYear <= MAX_YEAR
  ensures IsValidLocalDateTime(WithYear(dt, newYear))
{
  var newDay := DTUtils.ClampDay(newYear, dt.month, dt.day);
  FromComponents(newYear, dt.month, newDay, dt.hour, dt.minute, dt.second, dt.millisecond)
}
```

`ClampDay` ensures validity: February 29th, 2020 becomes February 28th, 2021 when changing to a non-leap year. This prevents invalid dates while maintaining predictable behavior.

### ZonedDateTime transformations

ZonedDateTime provides similar transformations, but they must account for timezone context. When changing date components, the offset may need to be recalculated if the new date falls in a different DST regime:

<!-- %no-check -->
```dafny
function WithYear(dt: ZonedDateTime, newYear: int32): ZonedDateTime
  requires IsValidZonedDateTime(dt) && MIN_YEAR <= newYear <= MAX_YEAR
  ensures IsValidZonedDateTime(WithYear(dt, newYear))
{
  ZonedDateTime(LDT.WithYear(dt.local, newYear), dt.zoneId, dt.offsetMinutes)
}
```


## Parsing with validation

### LocalDateTime parsing

<!-- %no-check -->
```dafny
datatype ParseFormat =
  | ISO8601       // yyyy-MM-ddTHH:mm:ss.fff
  | DateOnly      // yyyy-MM-dd

function Parse(text: string, format: ParseFormat): Result<LocalDateTime, string>
{
  match format {
    case ISO8601 => ParseISO8601(text)
    case DateOnly => ParseDateOnly(text)
  }
}
```

The ISO8601 parser validates in layers: length, separators, numeric components, range, and semantic validity. Each step provides descriptive error messages for malformed input.

### ZonedDateTime parsing

ZonedDateTime parsing is stricter, requiring explicit offset suffixes:

<!-- %no-check -->
```dafny
datatype ParseFormat =
  | ISO8601      // yyyy-MM-ddTHH:mm:ss.fffZ or yyyy-MM-ddTHH:mm:ss.fff±HH:mm
  | DateOnly     // yyyy-MM-ddZ or yyyy-MM-dd±HH:mm

function Parse(text: string, format: ParseFormat): Result<ZonedDateTime, string>
{
    match format {
        case ISO8601 => ParseISO8601(text)
        case DateOnly => ParseDateOnly(text)
    }
}

// Offset suffix: "Z" or "±HH:mm"
function ParseOffsetMinutesSuffix(suffix: string): Result<int, string>
{
    if |suffix| == 1 && suffix[0] == 'Z' then Success(0)
    else if |suffix| == 6 && (suffix[0] == '+' || suffix[0] == '-') && suffix[3] == ':' then
        …
    else Failure("Invalid offset: expected 'Z' or ±HH:mm")
}
```

ISO-8601 zoned format: `yyyy-MM-ddTHH:mm:ss.fffZ` or `yyyy-MM-ddTHH:mm:ss.fff±HH:mm` (length 24 or 29, with a 3-digit millisecond component and an explicit Z/offset suffix). Offset suffixes are validated and range-checked (±18:00, with 18:xx disallowed).


## Epoch-based arithmetic

We avoid calendar arithmetic complexity by converting to epoch milliseconds, performing math, then converting back. This provides consistency, simplicity, and verifiability.

### LocalDateTime arithmetic

For timezone-agnostic times, we convert to epoch milliseconds without timezone context (treating the local time as if it were UTC):

<!-- %no-check -->
```dafny
function Plus(dt: LocalDateTime, millisToAdd: int): Result<LocalDateTime, string>
  requires IsValidLocalDateTime(dt)
{
  var epochMillisResult := DTUtils.ToEpochTimeMilliseconds(
    dt.year, dt.month, dt.day, dt.hour, dt.minute, dt.second, dt.millisecond);
  if epochMillisResult.Failure? then
    Failure(epochMillisResult.error)
  else
    var newEpochMillis := epochMillisResult.value + millisToAdd;
    var components := DTUtils.FromEpochTimeMillisecondsFunc(newEpochMillis);
    if IsValidComponentRange(components) &&
       DTUtils.IsValidDateTime(components[0], components[1] as uint8,
                               components[2] as uint8, components[3] as uint8,
                               components[4] as uint8, components[5] as uint8,
                               components[6] as uint16) then
      Success(FromSequenceComponents(components))
    else
      Failure("Result date/time is out of valid range")
}
```

All convenience methods delegate to this core function:

<!-- %no-check -->
```dafny
function PlusDays(dt: LocalDateTime, days: int): Result<LocalDateTime, string>
{
  Plus(dt, days * (MILLISECONDS_PER_DAY as int))
}
```

### ZonedDateTime arithmetic: The critical difference

For timezone-aware times, epoch conversion accounts for the UTC offset. This is where ZonedDateTime gets more complex and interesting:

<!-- %no-check -->
```dafny
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
```

When adding time to a ZonedDateTime, we:
1. Convert the zoned time to UTC epoch milliseconds (accounting for offset)
2. Add the duration in milliseconds
3. Convert back to local components
4. Re-resolve the local time in the timezone (in case we crossed a DST boundary)

<!-- %no-check -->
```dafny
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
```

## Comparison

Both types provide lexicographic ordering and three-way comparison (-1, 0, 1).

### LocalDateTime comparison

<!-- %no-check -->
```dafny
function CompareLocal(dt1: LocalDateTime, dt2: LocalDateTime): int
{
  if dt1.year != dt2.year then
    if dt1.year < dt2.year then -1 else 1
  else if dt1.month != dt2.month then
    if dt1.month < dt2.month then -1 else 1
  // ... continues for all components
  else
    0
}
```

All comparison predicates (`IsBefore`, `IsAfter`, `IsEqual`) delegate to this single function, simplifying verification.

## Formatting

### LocalDateTime formatting

<!-- %no-check -->
```dafny
datatype DateFormat =
  | ISO8601                    // yyyy-MM-ddTHH:mm:ss.fff
  | DateOnly                   // yyyy-MM-dd
  | TimeOnly                   // HH:mm:ss
  | DateSlashDDMMYYYY          // dd/MM/yyyy

function Format(dt: LocalDateTime, format: DateFormat): string
  requires IsValidLocalDateTime(dt)
{
    match format
        case ISO8601 => ToString(dt)
        case DateOnly => /* ... */
        case TimeOnly => /* ... */
        case DateSlashDDMMYYYY => /* ... */
}
```

### ZonedDateTime formatting

ZonedDateTime formatting always includes an explicit offset suffix:

<!-- %no-check -->
```dafny
datatype DateFormat = ISO8601 | DateOnly

function ToStringSuffix(dt: ZonedDateTime): string
requires IsValidZonedDateTime(dt)
{
    if dt.offsetMinutes == 0 then "Z"
    else
        var absOffset := if dt.offsetMinutes < 0 then -dt.offsetMinutes else dt.offsetMinutes;
        var hh := absOffset / 60;
        var mm := absOffset % 60;
        var sign := if dt.offsetMinutes < 0 then "-" else "+";
        sign + (if hh < 10 then "0" + OfInt(hh as int) else OfInt(hh as int)) + ":" +
        (if mm < 10 then "0" + OfInt(mm as int) else OfInt(mm as int))
}

function Format(dt: ZonedDateTime, format: DateFormat): string
requires IsValidZonedDateTime(dt)
{
    match format
        case ISO8601 => LDT.ToString(dt.local) + ToStringSuffix(dt)
        case DateOnly =>
            var (y,m,d,,,,) := LDT.ToIntComponents(dt.local);
            OfInt(y) + "-" + DTUtils.PadWithZeros(m,2) + "-" +
            DTUtils.PadWithZeros(d,2) + ToStringSuffix(dt)
}
```


## Testing and integration

### LocalDateTime tests

<!-- %no-check -->
```dafny
method {:test} TestOfFunctionValidCases()
{
  var result1 := LDT.Of(2023, 6, 15, 14, 30, 45, 123);
  if result1.Success? {
    var dt1 := result1.value;
    AssertAndExpect(dt1.year == 2023 && dt1.month == 6 && dt1.day == 15);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt1));
  }

  var leapYearResult := LDT.Of(2020, 2, 29, 0, 0, 0, 0);
  expect leapYearResult.Success?;
}
```

### ZonedDateTime tests

ZonedDateTime tests document DST behavior explicitly:

<!-- %no-check -->
```dafny
method {:test} TestOfFunctionGapCase()
{
    var zoneId: string := "PST8PDT";
    var localA := LDT.LocalDateTime(2025, 3, 9, 2, 15, 0, 0);
    var pairA := ZDT.Of(zoneId, localA, ZDT.SHIFT_FORWARD);
    if pairA.0.Success? {
        var zdtA := pairA.0.value;
        AssertAndExpect(ZDT.IsValidZonedDateTime(zdtA));
        expect pairA.1 == ZDT.StatusGap;
        expect zdtA.offsetMinutes == -420; // PDT offset

        var format := ZDT.Format(pairA.0.value, ZDT.DateFormat.ISO8601);
        expect format == "2025-03-09T03:00:00.000-07:00";
    }
}
```

These tests both demonstrate usage and lock down behavior so downstream users can depend on it.

### Integration with Duration

Both modules integrate with the Duration library for rich temporal arithmetic:

<!-- %no-check -->
```dafny
function PlusDuration(dt: LocalDateTime, duration: Duration.Duration): Result<LocalDateTime, string>
{
  var totalMillis := (duration.seconds as int) * (MILLISECONDS_PER_SECOND as int) +
                     (duration.millis as int);
  Plus(dt, totalMillis)
}
```


## Platform interoperability

The only platform-dependent parts are:

* **ResolveLocal** — resolve a local wall clock time in zoneId with preference; detect Unique/Overlap/Gap; return (offset, normalized components).
* **NowZoned** — get current local components and the current offset.
* **GetNowZoneId** — get the system's local timezone ID.
* **Date-time ↔ epoch conversions** — provided by shared DateTime utilities.

In the reference .NET implementation:

* Gap shifts forward to the next valid minute when preference == SHIFT_FORWARD.
* Overlap compares UTC instants and chooses earlier/later based on the preference—robust for positive and negative offsets.
* TimeZoneInfo.Local.Id is used for the zone ID; cross-platform deployments should mind Windows vs. IANA identifiers.

## Looking ahead

The LocalDateTime and ZonedDateTime modules provide timezone-agnostic and timezone-aware temporal operations with formal verification guarantees. Future enhancements could include:

- **Calendar operations** for business days and holidays
- **Period arithmetic** with configurable overflow behavior
- **Format extensibility** for custom patterns and locales
- **Named-zone normalization** across platforms (Windows ↔ IANA)
- **Richer parsing/formatting** with token patterns and variable fractional seconds

These modules demonstrate how formal verification makes traditionally error-prone domains like date-time handling both safer and more reliable, while maintaining performance and usability.

Our hope is that these modules make time and timezone work boring—in the best possible way. *If it compiles and verifies, you can trust it.*


## The Duration companion library

Durations appear in nearly every timestamp-based calculation—from retries to billing intervals and performance metrics. The challenge isn't simple arithmetic; it's handling overflow, unit conversions, and composing time intervals reliably without losing precision or correctness.

The `Std.Duration` module provides a focused, practical companion to LocalDateTime and ZonedDateTime, handling time intervals with millisecond precision and strong specifications.

### Core representation

<!-- %no-check -->
```dafny
datatype Duration = Duration(
    seconds: int,
    millis: int
)

function ToTotalMilliseconds(d: Duration): int
{
    (d.seconds * MILLISECONDS_PER_SECOND_INT) + d.millis
}

function FromMilliseconds(ms: int): Duration
{
    var secondsValue := ms / MILLISECONDS_PER_SECOND_INT;
    var millisValue := ms % MILLISECONDS_PER_SECOND_INT;
    Duration(secondsValue, millisValue)
}
```

By normalizing through total milliseconds, we ensure consistent handling. This internal representation provides the foundation for all subsequent operations.

### Arithmetic operations

All duration arithmetic routes through milliseconds to prevent overflow and maintain precision:

<!-- %no-check -->
```dafny
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
    FromMilliseconds(ms1 - ms2)
}
```

### Parsing and formatting

Duration parsing follows ISO-8601: `PTxHyMz.wS` (for example, `PT2H30M45.500S` means 2 hours, 30 minutes, 45.5 seconds). Formatting produces the canonical representation with all components explicit.

### Integration with date-time

Duration composes naturally with both LocalDateTime and ZonedDateTime:

<!-- %no-check -->
```dafny
function EpochDifference(epoch1: int, epoch2: int): Duration
{
    var diff := if epoch1 >= epoch2 then (epoch1 - epoch2) as int
                else (epoch2 - epoch1) as int;
    FromMilliseconds(diff)
}
```

This enables seamless calculation of time deltas across date-time boundaries without precision loss.

## Acknowledgments

We would like to extend our sincere gratitude to **Robin Salkeld**, **Olivier Bouissou**, and **Mikael Mayer**, our points of contact and mentors at AWS. Their guidance on API design, performance optimization, and proof stability was instrumental in bringing these libraries to the Dafny community.
