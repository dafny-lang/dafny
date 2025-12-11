/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
Includes comprehensive test methods for validating the functionality of each
operation using Dafny's {:test} annotation.

These tests serve as verification examples that work with Dafny's formal proofs.
*/

module TestZonedDateTime {
  import opened Std.BoundedInts
  import opened Std.Wrappers
  import LDT = Std.LocalDateTime
  import Duration = Std.Duration
  import DTUtils = Std.DateTimeUtils
  import ZDT = Std.ZonedDateTime
  import opened Helpers

  method {:test} TestOfFunctionValidCases()
  {
    var ldt1 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var result1 := ZDT.Of("America/New_York", ldt1);
    if result1.0.Success? {
      var dt1 := result1.0.value;
      AssertAndExpect(ZDT.IsValidZonedDateTime(dt1));
      AssertAndExpect(LDT.IsValidLocalDateTime(dt1.local));
      AssertAndExpect(dt1.zoneId == "America/New_York");
      expect result1.1 == ZDT.StatusUnique;
    }
  }

  method {:test} TestOfFunctionGapCase()
  {
    var zoneId: string := "PST8PDT";
    var localA := LDT.LocalDateTime(2025, 3, 9, 2, 15, 0, 0);
    var pairA := ZDT.Of(zoneId, localA, ZDT.OverlapResolutionPreference.Error, ZDT.GapResolutionPreference.ShiftForward);
    if pairA.0.Success? {
      var zdtA := pairA.0.value;
      AssertAndExpect(ZDT.IsValidZonedDateTime(zdtA));
      expect pairA.1 == ZDT.StatusGap;
      expect zdtA.offsetMinutes == -420; // PDT offset

      var format := ZDT.Format(pairA.0.value, ZDT.DateFormat.ISO8601);
      expect format == "2025-03-09T03:00:00.000-07:00";
    }
  }

  method {:test} TestOfFunctionGapCase_Error()
  {
    var zoneId: string := "PST8PDT";
    var localB := LDT.LocalDateTime(2025, 3, 9, 2, 15, 0, 0);
    var pairB := ZDT.Of(zoneId, localB, ZDT.OverlapResolutionPreference.Error, ZDT.GapResolutionPreference.Error);
    expect pairB.0.Failure?;
    expect pairB.1 == ZDT.StatusError;
  }

  @ResourceLimit("1e7")
  method {:test} TestOfFunctionLeapYear()
  {
    var ldt2 := LDT.LocalDateTime(2020, 2, 29, 0, 0, 0, 0);
    var leapYearResult := ZDT.Of("America/New_York", ldt2);
    if leapYearResult.0.Success? {
      var leapDt := leapYearResult.0.value.local;
      expect LDT.IsValidLocalDateTime(leapDt);
    }
  }

  @ResourceLimit("1e7")
  method {:test} TestParseFunctionValid()
  {
    var validResult1 := ZDT.Parse("2023-06-15T14:30:45.123+08:00", ZDT.ParseFormat.ISO8601);
    if validResult1.Success? {
      var dt1 := validResult1.value;
      AssertAndExpect(ZDT.IsValidZonedDateTime(dt1));
    }
  }

  method {:test} TestParseFunctionWrongSeparators()
  {
    var invalidFormat1 := ZDT.Parse("2023/06/15 14:30:45+08:00", ZDT.ParseFormat.ISO8601);     // Wrong separators
    var invalidFormat2 := ZDT.Parse("2023-06-15+08:00", ZDT.ParseFormat.ISO8601);              // Too short

    expect invalidFormat1.Failure?;
    expect invalidFormat2.Failure?;
  }

  method {:test} TestParseFunctionMissingOffset()
  {
    var invalidFormat1 := ZDT.Parse("2023-06-15T14:30:45.123", ZDT.ParseFormat.ISO8601);
    var invalidFormat2 := ZDT.Parse("2023-06-15", ZDT.ParseFormat.DateOnly);
    expect invalidFormat1.Failure?;
    expect invalidFormat2.Failure?;
  }

  method {:test} TestParseFunctionISO8601_Z()
  {
    var r := ZDT.Parse("2023-06-15T14:30:45.123Z", ZDT.ParseFormat.ISO8601);
    expect r.Success?;
    if r.Success? {
      var dt := r.value;
      AssertAndExpect(ZDT.GetOffsetMinutes(dt) == 0);
      AssertAndExpect(|ZDT.GetZoneId(dt)| == 0);
    }
  }

  method {:test} TestParseFunctionDateOnly_Z()
  {
    var r := ZDT.Parse("2023-06-15Z", ZDT.ParseFormat.DateOnly);
    expect r.Success?;
    if r.Success? {
      var l := ZDT.GetLocalDateTime(r.value);
      AssertAndExpect(l.hour == 0 && l.minute == 0 && l.second == 0 && l.millisecond == 0);
      AssertAndExpect(ZDT.GetOffsetMinutes(r.value) == 0);
    }
  }

  method {:test} TestParseFunctionOffset_Edge_18h()
  {
    var ok := ZDT.Parse("2023-06-15T00:00:00.000+18:00", ZDT.ParseFormat.ISO8601);
    var bad := ZDT.Parse("2023-06-15T00:00:00.000+18:01", ZDT.ParseFormat.ISO8601);
    expect ok.Success?;
    expect bad.Failure?;
  }

  method {:test} {:resource_limit 2000000} TestToStringSuffix()
  {
    var ldt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var zdt := ZDT.ZonedDateTime(ldt, "Asia/Shanghai", 480);
    var isoStr := ZDT.ToStringSuffix(zdt);
    AssertAndExpect(isoStr == "+08:00");
  }

  @ResourceLimit("1e7")
  method {:test} TestFormatISO8601()
  {
    var ldt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var zdt := ZDT.ZonedDateTime(ldt, "Asia/Shanghai", 480);
    var isoFormat := ZDT.Format(zdt, ZDT.DateFormat.ISO8601);
    AssertAndExpect(isoFormat == "2023-06-15T14:30:45.123+08:00");
  }

  method {:test} {:resource_limit 5000000} TestFormatDateOnly()
  {
    var ldt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var zdt := ZDT.ZonedDateTime(ldt, "Asia/Shanghai", 480);
    var dateOnlyFormat := ZDT.Format(zdt, ZDT.DateFormat.DateOnly);
    AssertAndExpect(dateOnlyFormat == "2023-06-15+08:00");
  }

  method {:test} TestNowFunction() {
    var result := ZDT.Now();
    var zdt := ZDT.Now();
    if result.Success? {
      AssertAndExpect(ZDT.IsValidZonedDateTime(result.value));
    }
  }

  method {:test} TestGetters() {
    var ldt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 535);
    var zdt := ZDT.ZonedDateTime(ldt, "UTC", 0);
    AssertAndExpect(ZDT.IsValidZonedDateTime(zdt));
    AssertAndExpect(ZDT.GetYear(zdt) == 2023);
    AssertAndExpect(ZDT.GetMonth(zdt) == 3);
    AssertAndExpect(ZDT.GetDay(zdt) == 14);
    AssertAndExpect(ZDT.GetHour(zdt) == 15);
    AssertAndExpect(ZDT.GetMinute(zdt) == 9);
    AssertAndExpect(ZDT.GetSecond(zdt) == 26);
    AssertAndExpect(ZDT.GetMillisecond(zdt) == 535);
    AssertAndExpect(ZDT.GetLocalDateTime(zdt) == ldt);
    AssertAndExpect(ZDT.GetZoneId(zdt) == "UTC");
    AssertAndExpect(ZDT.GetOffsetMinutes(zdt) == 0);
  }

  method {:test} TestWithNormalCase() {
    var ldt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 535);
    var zdt := ZDT.ZonedDateTime(ldt, "UTC", 0);
    AssertAndExpect(ZDT.IsValidZonedDateTime(zdt));

    var zdt_with_new_year := ZDT.WithYear(zdt, 2024);
    AssertAndExpect(zdt_with_new_year.local.year == 2024);

    var zdt_with_new_month := ZDT.WithMonth(zdt, 2);
    AssertAndExpect(zdt_with_new_month.local.month == 2);

    var zdt_with_new_day := ZDT.WithDayOfMonth(zdt, 28);
    AssertAndExpect(zdt_with_new_day.local.day == 28);

    var zdt_with_new_hour := ZDT.WithHour(zdt, 10);
    AssertAndExpect(zdt_with_new_hour.local.hour == 10);

    var zdt_with_new_minute := ZDT.WithMinute(zdt, 30);
    AssertAndExpect(zdt_with_new_minute.local.minute == 30);

    var zdt_with_new_second := ZDT.WithSecond(zdt, 45);
    AssertAndExpect(zdt_with_new_second.local.second == 45);

    var zdt_with_new_millisecond := ZDT.WithMillisecond(zdt, 999);
    AssertAndExpect(zdt_with_new_millisecond.local.millisecond == 999);
  }

  method {:test} TestWithNotNormalCase() {
    var ldt1 := LDT.LocalDateTime(2020, 2, 29, 15, 9, 26, 535);
    var zdt1 := ZDT.ZonedDateTime(ldt1, "UTC", 0);
    AssertAndExpect(ZDT.IsValidZonedDateTime(zdt1));

    var zdt1_with_new_year := ZDT.WithYear(zdt1, 2021);
    expect zdt1_with_new_year.local.year == 2021;
    expect zdt1_with_new_year.local.day == 28; // Clamped to 28 since 2021 is not a leap year

    var ldt2 := LDT.LocalDateTime(2020, 3, 31, 15, 9, 26, 535);
    var zdt2 := ZDT.ZonedDateTime(ldt2, "UTC", 0);
    AssertAndExpect(ZDT.IsValidZonedDateTime(zdt2));

    var zdt2_with_new_month := ZDT.WithMonth(zdt2, 4);
    expect zdt2_with_new_month.local.month == 4;
    expect zdt2_with_new_month.local.day == 30; // Clamped to 30 since April has 30 days
  }

  method {:test} TestIsValidLocalDateTime() {
    var valid_ldt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 535);
    var valid_zdt := ZDT.ZonedDateTime(valid_ldt, "UTC", 0);
    AssertAndExpect(ZDT.IsValidZonedDateTime(valid_zdt));

    var invalid_month_ldt := LDT.LocalDateTime(2023, 13, 14, 15, 9, 26, 535);
    var invalid_month_zdt := ZDT.ZonedDateTime(invalid_month_ldt, "UTC", 0);
    AssertAndExpect(!ZDT.IsValidZonedDateTime(invalid_month_zdt));

    var invalid_hour_ldt := LDT.LocalDateTime(2023, 3, 14, 24, 9, 26, 535);
    var invalid_hour_zdt := ZDT.ZonedDateTime(invalid_hour_ldt, "UTC", 0);
    AssertAndExpect(!ZDT.IsValidZonedDateTime(invalid_hour_zdt));

    var invalid_minute_ldt := LDT.LocalDateTime(2023, 3, 14, 15, 60, 26, 535);
    var invalid_minute_zdt := ZDT.ZonedDateTime(invalid_minute_ldt, "UTC", 0);
    AssertAndExpect(!ZDT.IsValidZonedDateTime(invalid_minute_zdt));

    var invalid_second_ldt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 61, 535);
    var invalid_second_zdt := ZDT.ZonedDateTime(invalid_second_ldt, "UTC", 0);
    AssertAndExpect(!ZDT.IsValidZonedDateTime(invalid_second_zdt));

    var invalid_millisecond_ldt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 1000);
    var invalid_millisecond_zdt := ZDT.ZonedDateTime(invalid_millisecond_ldt, "UTC", 0);
    AssertAndExpect(!ZDT.IsValidZonedDateTime(invalid_millisecond_zdt));
  }

  method {:test} TestToEpochTimeMilliseconds() {
    // Test converting LocalDateTime to epoch time milliseconds
    var ldt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var zdt := ZDT.ZonedDateTime(ldt, "PST8PDT", -420);
    AssertAndExpect(ZDT.IsValidZonedDateTime(zdt));

    var epochResult := ZDT.ToEpochTimeMilliseconds(zdt.local.year, zdt.local.month, zdt.local.day,
                                                   zdt.local.hour, zdt.local.minute, zdt.local.second,
                                                   zdt.local.millisecond, zdt.offsetMinutes);
    expect epochResult.Success?;
    if epochResult.Success? {
      var epochMillis := epochResult.value;
      // Verify we can convert back
      var components := ZDT.FromEpochTimeMillisecondsFunc(epochMillis, zdt.offsetMinutes);
      expect |components| == 7;
      expect components[0] == zdt.local.year;
      expect components[1] == zdt.local.month as int32;
      expect components[2] == zdt.local.day as int32;
      expect components[3] == zdt.local.hour as int32;
      expect components[4] == zdt.local.minute as int32;
      expect components[5] == zdt.local.second as int32;
      expect components[6] == zdt.local.millisecond as int32;
    }
  }

  method {:test} TestComprehensivePlusOperations() {
    // Comprehensive test for all plus operations with Result handling
    var baseLDT := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var baseZDT := ZDT.ZonedDateTime(baseLDT, "", -420);
    AssertAndExpect(ZDT.IsValidZonedDateTime(baseZDT));

    // Test PlusDays
    var plusDaysResult := ZDT.PlusDays(baseZDT, 20);
    expect plusDaysResult.Success?;
    if plusDaysResult.Success? {
      var result := plusDaysResult.value;
      expect result.local.month == 7;
      expect result.local.day == 5;
    }

    // Test PlusHours
    var plusHoursResult := ZDT.PlusHours(baseZDT, 25);
    expect plusHoursResult.Success?;
    if plusHoursResult.Success? {
      var result := plusHoursResult.value;
      expect result.local.day == 16;
      expect result.local.hour == 15;
    }

    // Test PlusMinutes
    var plusMinutesResult := ZDT.PlusMinutes(baseZDT, 90);
    expect plusMinutesResult.Success?;
    if plusMinutesResult.Success? {
      var result := plusMinutesResult.value;
      expect result.local.hour == 16;
      expect result.local.minute == 0;
    }

    // Test PlusSeconds
    var plusSecondsResult := ZDT.PlusSeconds(baseZDT, 120);
    expect plusSecondsResult.Success?;
    if plusSecondsResult.Success? {
      var result := plusSecondsResult.value;
      expect result.local.minute == 32;
      expect result.local.second == 45;
    }

    // Test PlusMilliseconds
    var plusMillisecondsResult := ZDT.PlusMilliseconds(baseZDT, 2000);
    expect plusMillisecondsResult.Success?;
    if plusMillisecondsResult.Success? {
      var result := plusMillisecondsResult.value;
      expect result.local.second == 47;
      expect result.local.millisecond == 123;
    }

    // Test PlusDuration
    var duration := Duration.Duration(0, 2_000); // 2 seconds
    var plusDurationResult := ZDT.PlusDuration(baseZDT, duration);
    expect plusDurationResult.Success?;
    if plusDurationResult.Success? {
      var result := plusDurationResult.value;
      expect result.local.second == 47;
      expect result.local.millisecond == 123;
    }
  }

  method {:test} TestComprehensiveMinusOperations() {
    // Comprehensive test for all minus operations with Result handling
    var baseLDT := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var baseZDT := ZDT.ZonedDateTime(baseLDT, "", -420);
    AssertAndExpect(ZDT.IsValidZonedDateTime(baseZDT));

    // Test MinusDays
    var minusDaysResult := ZDT.MinusDays(baseZDT, 20);
    expect minusDaysResult.Success?;
    if minusDaysResult.Success? {
      var result := minusDaysResult.value;
      expect result.local.month == 5;
      expect result.local.day == 26;
    }

    // Test MinusHours
    var minusHoursResult := ZDT.MinusHours(baseZDT, 15);
    expect minusHoursResult.Success?;
    if minusHoursResult.Success? {
      var result := minusHoursResult.value;
      expect result.local.day == 14;
      expect result.local.hour == 23;
    }

    // Test MinusMinutes
    var minusMinutesResult := ZDT.MinusMinutes(baseZDT, 45);
    expect minusMinutesResult.Success?;
    if minusMinutesResult.Success? {
      var result := minusMinutesResult.value;
      expect result.local.hour == 13;
      expect result.local.minute == 45;
    }

    // Test MinusSeconds
    var minusSecondsResult := ZDT.MinusSeconds(baseZDT, 1000);
    expect minusSecondsResult.Success?;
    if minusSecondsResult.Success? {
      var result := minusSecondsResult.value;
      expect result.local.minute == 14;
      expect result.local.second == 5;
    }

    // Test MinusMilliseconds
    var minusMillisecondsResult := ZDT.MinusMilliseconds(baseZDT, 200);
    expect minusMillisecondsResult.Success?;
    if minusMillisecondsResult.Success? {
      var result := minusMillisecondsResult.value;
      expect result.local.second == 44;
      expect result.local.millisecond == 923;
    }

    // Test MinusDuration
    var duration := Duration.Duration(0, 3_000); // 3 seconds
    var minusDurationResult := ZDT.MinusDuration(baseZDT, duration);
    expect minusDurationResult.Success?;
    if minusDurationResult.Success? {
      var result := minusDurationResult.value;
      expect result.local.second == 42;
      expect result.local.millisecond == 123;
    }
  }
}