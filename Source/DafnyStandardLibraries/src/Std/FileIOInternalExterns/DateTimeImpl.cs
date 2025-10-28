using System;
using System.Linq;
using System.Numerics;
using Dafny;

public static class DateTimeImpl
{
    public static ISequence<int> GetNowComponents()
    {
        var now = DateTime.Now;
        var components = new int[]
        {
            now.Year,
            now.Month,
            now.Day,
            now.Hour,
            now.Minute,
            now.Second,
            now.Millisecond,
        };

        return Sequence<int>.FromArray(components);
    }

    public static BigInteger ToEpochTimeMilliseconds(
        int year,
        uint month,
        uint day,
        uint hour,
        uint minute,
        uint second,
        uint millisecond,
        TimeSpan? offset = null
    )
    {
        return new DateTimeOffset(
            year,
            (int)month,
            (int)day,
            (int)hour,
            (int)minute,
            (int)second,
            (int)millisecond,
            offset ?? TimeSpan.Zero
        ).ToUnixTimeMilliseconds();
    }

    public static ISequence<int> FromEpochTimeMilliseconds(
        BigInteger epochMilliseconds,
        TimeSpan? offset = null
    )
    {
        DateTimeOffset dateTimeOffset = DateTimeOffset
            .FromUnixTimeMilliseconds((long)epochMilliseconds)
            .ToOffset(offset ?? TimeSpan.Zero);
        var components = new int[]
        {
            dateTimeOffset.Year,
            dateTimeOffset.Month,
            dateTimeOffset.Day,
            dateTimeOffset.Hour,
            dateTimeOffset.Minute,
            dateTimeOffset.Second,
            dateTimeOffset.Millisecond,
        };
        return Sequence<int>.FromArray(components);
    }

    public static bool IsLeapYear(BigInteger year)
    {
        return DateTime.IsLeapYear((int)year);
    }
}
