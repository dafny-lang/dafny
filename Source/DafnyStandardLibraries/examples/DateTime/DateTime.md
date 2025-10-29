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

## File Descriptions

## Function Descriptions

## Test Commands

```bash
dafny test --target:cs --standard-libraries Source/DafnyStandardLibraries/examples/DateTime/DurationExamples.dfy --allow-warnings
```
