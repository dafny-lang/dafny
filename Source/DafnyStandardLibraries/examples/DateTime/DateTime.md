# LocalDateTime

dafny test --target:cs --standard-libraries Source/DafnyStandardLibraries/examples/DateTime/LocalDateTimeExamples.dfy Source/DafnyStandardLibraries/src/Std/FileIOInternalExterns/DateTimeImpl.cs --allow-warnings

dafny test --target:cs --standard-libraries Source/DafnyStandardLibraries/examples/DateTime/DurationTimeExamples.dfy --allow-warnings


Regarding the "absence of leap years every 4000 years," I checked how major programming languages determine leap years and found that none of them use the 4000-year rule. I think we can ignore this very rare rule.

The date calculation logic is now based on epoch time, so we have already avoided a lot of unnecessarily complex date-handling logic.

The new logic first converts the LocalDateTime to an epoch time in milliseconds. It also converts the time to be added or subtracted into milliseconds. Then, it performs the addition or subtraction. Finally, it converts the resulting millisecond time back to a LocalDateTime.

## Execute Verification

```
dafny test --target:cs --standard-libraries LocalDateTime.dfy LocalDateTimeExamples.dfy  DateTimeImpl.cs --allow-warnings
```

## Run Test
```
dafny build LocalDateTimeExamples.dfy --target:cs LocalDateTimeExamples.dfy DateTimeImpl.cs --standard-libraries
./LocalDateTimeExamples
```



# Duration
The Duration module provides formally verified operations for representing and manipulating time durations in Dafny.
It ensures mathematical correctness using contracts (requires, ensures) and safe overflow handling via bounded integer arithmetic.
This module underpins temporal computations in the LocalDateTime system by enabling precise duration arithmetic and comparisons.
## File Descriptions
Duration.dfy
Defines the Duration datatype and all associated functions for creation, arithmetic, comparison, and conversion.
Includes proof contracts ensuring that duration values always satisfy the validity predicate (millis < 1000).
Provides robust overflow handling using 64-bit intermediate computations to maintain correctness within 32-bit bounds.
DurationExamples.dfy
Contains verified test examples that demonstrate and validate all major operations in the Duration module.
These tests use Dafny’s {:test} annotation for proof-based execution and formal validation.

## Function Descriptions

- **Datatype Definition**  
datatype Duration = Duration(seconds: uint32, millis: uint32)
Represents a duration as a combination of seconds and milliseconds.
- **Creation Functions**  
 -`FromMilliseconds(ms: uint32)`:Converts a millisecond value into a valid Duration, splitting it into seconds and leftover milliseconds.
 -`FromSeconds(s: uint32)`:Creates a Duration equivalent to the given number of seconds.
 -`FromMinutes(m: uint32)`,-`FromHours(h: uint32)`, -`FromDays(d: uint32)`: Scales minutes, hours, or days into milliseconds and constructs a valid duration object.
- **Arithmetic Operations**  
 -`Plus(d1, d2) / Minus(d1, d2)`: Performs addition or subtraction of two durations, clamping results to 32-bit maximums. Minus returns zero duration if the result would be negative.
 -`Scale(d, factor)`: Multiplies a duration by an integer factor, with overflow protection.
 -`Divide(d, divisor)`: Divides a duration by a positive integer, truncating fractional parts.
 -`Mod(d1, d2)`: Computes the remainder of one duration divided by another.
- **Comparison Functions**
 -`Compare(d1, d2)`: Returns -1, 0, or 1 to indicate whether d1 is less than, equal to, or greater than d2.
 -`Less(d1, d2) / LessOrEqual(d1, d2)`: Boolean predicates for ordering durations.
 -`Max(d1, d2) / Min(d1, d2)`: Returns the greater or lesser of two durations.
 -`MaxSeq(durs) / MinSeq(durs)`: Computes the maximum or minimum duration from a non-empty sequence using recursive helper functions with termination proofs.
- **Conversion Functions**  
 -`ToTotalMilliseconds(d)`: Converts a duration to total milliseconds as a 32-bit integer with overflow handling.
 -`ToTotalSeconds(d), ToTotalMinutes(d), ToTotalHours(d), ToTotalDays(d)`: Converts the duration into progressively larger time units using constant ratios.
 -`ConvertToUnit(d, unitMs)`: Converts a duration into arbitrary units defined by the given millisecond base.
- **Accessors**
 -`GetSeconds(d), GetMilliseconds(d)`:Returns individual components of the duration.
- **Formatting and Parsing**
 -`ToString(d)`: Converts a duration into an ISO 8601–compliant string of the form PT#H#M#S.sssS.
 -`ParseString(text)`: Parses a duration string in ISO 8601 format (PT#H#M#S.sssS) into a valid Duration.
Includes helper functions for parsing numeric substrings (ParseNumericString, ParseComponent) and locating delimiters (FindCharOrNeg).
- **Internal helper functions**
 -`FindCharOrNeg(text, ch)` → Finds a character or returns -1.
 -`IsNumeric(s)` → Checks if all characters in a string are digits.
 -`Pow10(n)` → Computes 10ⁿ recursively for numeric parsing.
- **Derived Computation**
 -`EpochDifference(epoch1, epoch2)`: Computes the absolute duration difference between two epoch millisecond timestamps, returning a valid Duration instance.
- **Test Commands**
dafny test --target:cs --standard-libraries Source/DafnyStandardLibraries/examples/DateTime/DurationExamples.dfy --allow-warnings
This command runs Dafny’s formal verification and executable tests for all Duration operations, ensuring correctness in both logic and implementation.
