namespace DateTimeImpl
{
  using System.Numerics;
  using Dafny;

  public static class __default
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

    public static _System._ITuple3<
      bool,
      BigInteger,
      ISequence<Dafny.Rune>
    > INTERNAL__ToEpochTimeMilliseconds(
      int year,
      uint month,
      uint day,
      uint hour,
      uint minute,
      uint second,
      uint millisecond,
      int? offsetMinutes = null
    )
    {
      try
      {
        var offset = TimeSpan.Zero;
        if (offsetMinutes != null)
        {
          offset = TimeSpan.FromMinutes((double)offsetMinutes);
        }
        var epochMilliseconds = new DateTimeOffset(
          year,
          (int)month,
          (int)day,
          (int)hour,
          (int)minute,
          (int)second,
          (int)millisecond,
          offset
        ).ToUnixTimeMilliseconds();

        return _System.Tuple3<bool, BigInteger, ISequence<Dafny.Rune>>.create(
          false,
          epochMilliseconds,
          Sequence<Rune>.Empty
        );
      }
      catch (Exception e)
      {
        return _System.Tuple3<bool, BigInteger, ISequence<Dafny.Rune>>.create(
          true,
          0,
          Sequence<Rune>.UnicodeFromString(e.Message)
        );
      }
    }

    public static ISequence<int> FromEpochTimeMilliseconds(
      BigInteger epochMilliseconds,
      int? offsetMinutes = null
    )
    {
      var offset = TimeSpan.Zero;
      if (offsetMinutes != null)
      {
        offset = TimeSpan.FromMinutes((double)offsetMinutes);
      }
      DateTimeOffset dateTimeOffset = DateTimeOffset
        .FromUnixTimeMilliseconds((long)epochMilliseconds)
        .ToOffset(offset);
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
}
