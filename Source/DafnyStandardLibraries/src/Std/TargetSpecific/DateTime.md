# LocalDateTime module

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

# Duration module

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