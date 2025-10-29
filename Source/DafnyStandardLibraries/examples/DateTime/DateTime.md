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