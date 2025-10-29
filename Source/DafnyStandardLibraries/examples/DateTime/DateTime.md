# LocalDateTime module

The `LocalDateTime` module provides formally verified date and time functionality in Dafny without timezone information.  
It ensures correctness using contracts (`requires`, `ensures`) and supports proof-based reasoning for temporal computations.

## File Descriptions

- **`LocalDateTime.dfy`**  
  Contains the full implementation of LocalDateTime operations, including creation, parsing, formatting, arithmetic, and comparison functions.  
  It defines all verification contracts and imports external DateTime utilities. Uses epoch-time-based calculations for reliable date arithmetic.

- **`LocalDateTimeExamples.dfy`**  
  Includes comprehensive test methods for validating the functionality of each operation using Dafny's `{:test}` annotation.  
  These tests serve as verification examples that work with Dafny's formal proofs.

- **`DateTimeImpl.cs`**  
  Provides external implementations of core datetime operations, particularly epoch time conversions, leap year calculations, and current time access.

- **`DateTimeUtils.dfy`**  
  Contains utility functions for date validation, day calculations, and formatting helpers.

- **`DateTimeConstant.dfy`**  
  Defines time-related constants and bounded integer types used throughout the module.

## Function Descriptions

- **Creation Functions**  
  - `Of()`: Creates a LocalDateTime from individual components with validation
  - `Now()`: Returns the current local date and time
  - `FromSequenceComponents()`: Creates from a sequence of integer components

- **Parsing Functions**  
  - `Parse()`: Parses strings in ISO8601 or DateOnly formats
  - `ParseISO8601()`: Specifically handles "YYYY-MM-DDTHH:mm:ss.fff" format
  - `ParseDateOnly()`: Handles "YYYY-MM-DD" format with time defaulting to midnight

- **Arithmetic Operations**  
  - `Plus/Minus` functions for days, hours, minutes, seconds, milliseconds
  - `PlusDuration()/MinusDuration()`: Add or subtract Duration objects
  - All operations use epoch-time conversion for accuracy across month/year boundaries

- **Formatting Functions**  
  - `ToString()`: Default ISO8601 string representation
  - `Format()`: Supports multiple formats (ISO8601, DateOnly, TimeOnly, etc.)

- **Comparison Functions**  
  - `CompareLocal()`: Returns -1, 0, or 1 for ordering
  - `IsBefore()`, `IsAfter()`, `IsEqual()`: Boolean comparison predicates

- **Modification Functions**  
  - `With` functions: Create new instances with modified components (year, month, day, etc.)
  - Automatically handles date clamping (e.g., Feb 29 → Feb 28 in non-leap years)

- **Getter Functions**  
  - Individual component accessors: `GetYear()`, `GetMonth()`, `GetDay()`, etc.
  - `IsValidLocalDateTime()`: Validates a LocalDateTime instance

## Test Commands

```bash
dafny test --target:cs --standard-libraries Source/DafnyStandardLibraries/examples/DateTime/LocalDateTimeExamples.dfy Source/DafnyStandardLibraries/src/Std/FileIOInternalExterns/DateTimeImpl.cs --allow-warnings
```

# Duration

The file defines a Duration module that implements a robust set of time duration utilities in Dafny.

It models durations data structure and provides:
- Arithmetic operations (add, subtract, scale, divide)
- Comparisons (less than, max, min)
- Conversions between time units (milliseconds, seconds, minutes, hours, days)
- String formatting and parsing for simplified ISO-8601–like time strings (e.g. "PT9650H30M")
- Helper functions for sequence scanning (like StringIndexOf)

## How to execute Duration Test Sample

```
dafny build TestDuration.dfy --standard-libraries
./TestLocalDateTime
```

# ZonedDateTime
## Initial Design of ZonedDateTime API (Pseudocode)

The initial design of ZonedDateTime will use Dafny's {:extern} hook to interface with C#, enable C# to utilize .NET's TimeZoneInfo and DateTimeOffset to handle time zone rules + DST (Unique/Overlap/GAP), and return the "parsed/normalized" results back to Dafny.

The Zoned Date Time will have a datatype that stores the LocalDateTime datatype, a zoneId obtained from .NET's TimeZoneInfo, and an offsetMinutes obtained from .NET's DateTimeOffset. 


To resolve the local date time, we will first use the timezone from zoneId to determine the local date time is valid or not. If the local date time is not valid, it could be during spring DST transition. Therefore, we have to shift forward to the next valid time. If the local date time is ambiguous, we will choose either the earlier time or the later time based on the preference defined by the zoned date time.

## How to execute ZonedDateTime Test Sample

```
dafny build TestZonedDateTime.dfy --target:cs TestZonedDateTime.dfy DateTimeImpl.cs ZonedDateTimeImpl.cs --standard-libraries
./TestZonedDateTime
```

**Current Questions:**

1.	Is ShiftForward the desired policy for Gap times, or rejection or a different normalization?
2.  For Overlap times, what should be our default preference (PreferEarlier vs PreferLater) if the caller doesn’t specify?