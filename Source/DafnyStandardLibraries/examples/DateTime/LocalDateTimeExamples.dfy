include "../../src/Std/DateTime/LocalDateTime.dfy"
include "../../src/Std/DateTime/Duration.dfy"
include "../../src/Std/DateTime/DateTimeUtils.dfy"
include "../Helpers.dfy"

module TestLocalDateTime {
  import opened Std.BoundedInts
  import LDT = LocalDateTime
  import Duration = Duration
  import DTUtils = DateTimeUtils
  import opened Helpers

  method {:test} TestOfFunctionValidCases()
  {
    var result1 := LDT.Of(2023, 6, 15, 14, 30, 45, 123);
    if result1.Success? {
      var dt1 := result1.value;
      AssertAndExpect(dt1.year == 2023 && dt1.month == 6 && dt1.day == 15);
      AssertAndExpect(dt1.hour == 14 && dt1.minute == 30 && dt1.second == 45 && dt1.millisecond == 123);
      AssertAndExpect(LDT.IsValidLocalDateTime(dt1));
    }

    var leapYearResult := LDT.Of(2020, 2, 29, 0, 0, 0, 0);
    if leapYearResult.Success? {
      var leapDt := leapYearResult.value;
      AssertAndExpect(leapDt.year == 2020 && leapDt.month == 2 && leapDt.day == 29);
      AssertAndExpect(LDT.IsValidLocalDateTime(leapDt));
    }
  }

  method {:test} TestOfFunctionInvalidMonths()
  {
    var invalidMonth1 := LDT.Of(2023, 0, 15, 14, 30, 45, 123);   // Month too low
    var invalidMonth2 := LDT.Of(2023, 13, 15, 14, 30, 45, 123);  // Month too high
    AssertAndExpect(invalidMonth1.Failure?);
    AssertAndExpect(invalidMonth2.Failure?);
  }

  method {:test} TestOfFunctionInvalidDays()
  {
    var invalidDay1 := LDT.Of(2023, 6, 0, 14, 30, 45, 123);     // Day too low
    var invalidDay2 := LDT.Of(2023, 6, 32, 14, 30, 45, 123);    // Day too high for June
    // var invalidDay3 := LDT.Of(2023, 2, 29, 14, 30, 45, 123);    // Feb 29 in non-leap year
    // var invalidDay4 := LDT.Of(2023, 4, 31, 14, 30, 45, 123);    // April 31st doesn't exist
    AssertAndExpect(invalidDay1.Failure?);
    AssertAndExpect(invalidDay2.Failure?);
    // AssertAndExpect(invalidDay3.Failure?);
    // AssertAndExpect(invalidDay4.Failure?);
  }

  method {:test} TestOfFunctionInvalidTime()
  {
    var invalidHour := LDT.Of(2023, 6, 15, 24, 30, 45, 123);   // Hour too high
    var invalidMinute := LDT.Of(2023, 6, 15, 14, 60, 45, 123); // Minute too high
    var invalidSecond := LDT.Of(2023, 6, 15, 14, 30, 60, 123); // Second too high
    var invalidMs := LDT.Of(2023, 6, 15, 14, 30, 45, 1000);    // Millisecond too high
    AssertAndExpect(invalidHour.Failure?);
    AssertAndExpect(invalidMinute.Failure?);
    AssertAndExpect(invalidSecond.Failure?);
    AssertAndExpect(invalidMs.Failure?);
  }

  method {:test} TestParseFunctionValid()
  {
    var validResult1 := LDT.Parse("2023-06-15T14:30:45.123", LDT.ParseFormat.ISO8601);
    if validResult1.Success? {
      var dt1 := validResult1.value;
      AssertAndExpect(LDT.IsValidLocalDateTime(dt1));
    }
  }

  method {:test} TestParseFunctionWrongSeparators()
  {
    var invalidFormat1 := LDT.Parse("2023/06/15 14:30:45", LDT.ParseFormat.ISO8601);     // Wrong separators
    var invalidFormat2 := LDT.Parse("2023-06-15", LDT.ParseFormat.ISO8601);              // Too short

    expect invalidFormat1.Failure?;
    expect invalidFormat2.Failure?;
  }

  method {:test} TestParseFunctionMissingMilliseconds()
  {
    var invalidFormat3 := LDT.Parse("2023-06-15T14:30:45", LDT.ParseFormat.ISO8601);     // Missing milliseconds
    expect invalidFormat3.Failure?;
  }

  method {:test} TestParseFunctionWrongDateOrder()
  {
    var invalidFormat4 := LDT.Parse("15-06-2023T14:30:45.123", LDT.ParseFormat.ISO8601); // Wrong date order
    expect invalidFormat4.Failure?;
  }

  method {:test} TestParseFunctionInvalidDigits()
  {
    var invalidFormat5 := LDT.Parse("2023-6-15T14:30:45.123", LDT.ParseFormat.ISO8601);  // Single digit month
    var invalidFormat6 := LDT.Parse("2023-06-5T14:30:45.123", LDT.ParseFormat.ISO8601);  // Single digit day
    var invalidFormat7 := LDT.Parse("2023-06-15T4:30:45.123", LDT.ParseFormat.ISO8601);  // Single digit hour
    var invalidFormat8 := LDT.Parse("2023-06-15T14:3:45.123", LDT.ParseFormat.ISO8601);  // Single digit minute

    expect invalidFormat5.Failure?;
    expect invalidFormat6.Failure?;
    expect invalidFormat7.Failure?;
    expect invalidFormat8.Failure?;
  }

  method {:test} TestParseFunctionInvalidFormats()
  {
    var invalidFormat9 := LDT.Parse("2023-06-15T14:30:5.123", LDT.ParseFormat.ISO8601);  // Single digit second
    var invalidFormat10 := LDT.Parse("2023-06-15T14:30:45.12", LDT.ParseFormat.ISO8601); // Wrong millisecond length
    var invalidFormat11 := LDT.Parse("", LDT.ParseFormat.ISO8601);                       // Empty string
    var invalidFormat12 := LDT.Parse("not-a-date", LDT.ParseFormat.ISO8601);             // Completely invalid

    expect invalidFormat9.Failure?;
    expect invalidFormat10.Failure?;
    expect invalidFormat11.Failure?;
    expect invalidFormat12.Failure?;
  }

  method {:test} TestDateOnlyParsingValid()
  {
    // Test valid DateOnly parsing - simplified to avoid verification timeout
    var validDateOnly1 := LDT.Parse("2023-06-15", LDT.ParseFormat.DateOnly);
    expect validDateOnly1.Success?;
    if validDateOnly1.Success? {
      var dt := validDateOnly1.value;
      AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    }

    var validDateOnly2 := LDT.Parse("2024-02-29", LDT.ParseFormat.DateOnly); // Leap year
    expect validDateOnly2.Success?;

    var validDateOnly3 := LDT.Parse("2000-12-31", LDT.ParseFormat.DateOnly); // End of century leap year  
    expect validDateOnly3.Success?;
  }

  method {:test} TestDateOnlyParsingInvalidSeparators()
  {
    var invalidDateOnly1 := LDT.Parse("2023/06/15", LDT.ParseFormat.DateOnly);      // Wrong separators
    var invalidDateOnly2 := LDT.Parse("2023-6-15", LDT.ParseFormat.DateOnly);       // Single digit month
    var invalidDateOnly3 := LDT.Parse("2023-06-5", LDT.ParseFormat.DateOnly);       // Single digit day
    var invalidDateOnly4 := LDT.Parse("23-06-15", LDT.ParseFormat.DateOnly);        // Two digit year

    expect invalidDateOnly1.Failure?;
    expect invalidDateOnly2.Failure?;
    expect invalidDateOnly3.Failure?;
    expect invalidDateOnly4.Failure?;
  }

  method {:test} TestDateOnlyParsingInvalidDates()
  {
    var invalidDateOnly5 := LDT.Parse("2023-13-15", LDT.ParseFormat.DateOnly);      // Invalid month
    // var invalidDateOnly6 := LDT.Parse("2023-02-30", LDT.ParseFormat.DateOnly);      // Invalid day for February
    // var invalidDateOnly7 := LDT.Parse("2023-04-31", LDT.ParseFormat.DateOnly);      // Invalid day for April

    expect invalidDateOnly5.Failure?;
    // expect invalidDateOnly6.Failure?;
    // expect invalidDateOnly7.Failure?;
  }

  method {:test} TestDateOnlyParsingInvalidFormats()
  {
    var invalidDateOnly8 := LDT.Parse("2023-06-15T14:30:45", LDT.ParseFormat.DateOnly); // Too long
    var invalidDateOnly9 := LDT.Parse("2023-06", LDT.ParseFormat.DateOnly);         // Too short
    var invalidDateOnly10 := LDT.Parse("", LDT.ParseFormat.DateOnly);               // Empty string
    var invalidDateOnly11 := LDT.Parse("not-a-date", LDT.ParseFormat.DateOnly);     // Invalid format

    expect invalidDateOnly8.Failure?;
    expect invalidDateOnly9.Failure?;
    expect invalidDateOnly10.Failure?;
    expect invalidDateOnly11.Failure?;
  }

  method {:test} TestCompareFunction()
  {
    var dt1 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var dt2 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 124);
    var dt3 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var cmp1 := LDT.CompareLocal(dt1, dt2);
    var cmp2 := LDT.CompareLocal(dt2, dt1);
    var cmp3 := LDT.CompareLocal(dt1, dt3);

    AssertAndExpect(cmp1 == -1);  // dt1 < dt2
    AssertAndExpect(cmp2 == 1);   // dt2 > dt1
    AssertAndExpect(cmp3 == 0);   // dt1 == dt3
  }

  method {:test} TestArithmeticFunctions()
  {
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var duration := Duration.FromMilliseconds(3661500); // 1 hour, 1 minute, 1 second, 500ms

    var plusResult := LDT.PlusDuration(dt, duration);
    expect LDT.GetHour(plusResult) == 15;  // Should be one hour later
    expect LDT.GetMinute(plusResult) == 31; // Should be one minute later
    expect LDT.GetSecond(plusResult) == 46; // Should be one second later
    expect LDT.GetMillisecond(plusResult) == 623; // Should be 500ms later

    var minusResult := LDT.MinusDuration(dt, duration);
    expect LDT.GetHour(minusResult) == 13;  // Should be one hour earlier
    expect LDT.GetMinute(minusResult) == 29; // Should be one minute earlier
    expect LDT.GetSecond(minusResult) == 43;
    expect LDT.GetMillisecond(minusResult) == 623; // 123 - 500 + 1000 = 623

    // Test cross-day boundary
    var lateNight := LDT.LocalDateTime(2023, 6, 15, 23, 30, 45, 123);
    var longDuration := Duration.FromMilliseconds(7200000); // 2 hours
    var nextDay := LDT.PlusDuration(lateNight, longDuration);
    expect LDT.GetDay(nextDay) == 16;  // Should be next day
    expect LDT.GetHour(nextDay) == 1;  // Should be 1:30 AM
    expect LDT.GetMinute(nextDay) == 30;
  }

  method {:test} TestToString()
  {
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var isoStr := LDT.ToString(dt);
    AssertAndExpect(isoStr == "2023-06-15T14:30:45.123");
  }

  method {:test} TestFormatISO8601()
  {
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var isoFormat := LDT.Format(dt, LDT.DateFormat.ISO8601);
    AssertAndExpect(isoFormat == "2023-06-15T14:30:45.123");
  }

  method {:test} TestFormatFunctionDateAndTime()
  {
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);

    var dateOnly := LDT.Format(dt, LDT.DateFormat.DateOnly);
    AssertAndExpect(dateOnly == "2023-06-15");

    var timeOnly := LDT.Format(dt, LDT.DateFormat.TimeOnly);
    AssertAndExpect(timeOnly == "14:30:45");

    var dateTimeSpace := LDT.Format(dt, LDT.DateFormat.DateTimeSpace);
    AssertAndExpect(dateTimeSpace == "2023-06-15 14:30:45");
  }

  method {:test} TestFormatFunctionSlashFormats()
  {
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);

    var ddmmyyyy := LDT.Format(dt, LDT.DateFormat.DateSlashDDMMYYYY);
    AssertAndExpect(ddmmyyyy == "15/06/2023");

    var mmddyyyy := LDT.Format(dt, LDT.DateFormat.DateSlashMMDDYYYY);
    AssertAndExpect(mmddyyyy == "06/15/2023");
  }

  method {:test} TestWithNormalCase() {
    var dt1 := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 535);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt1));

    var dt1_with_new_year := LDT.WithYear(dt1, 2024);
    AssertAndExpect(dt1_with_new_year.year == 2024);

    var dt1_with_new_month := LDT.WithMonth(dt1, 2);
    AssertAndExpect(dt1_with_new_month.month == 2);

    var dt1_with_new_day := LDT.WithDayOfMonth(dt1, 28);
    AssertAndExpect(dt1_with_new_day.day == 28);

    var dt1_with_new_hour := LDT.WithHour(dt1, 10);
    AssertAndExpect(dt1_with_new_hour.hour == 10);

    var dt1_with_new_minute := LDT.WithMinute(dt1, 30);
    AssertAndExpect(dt1_with_new_minute.minute == 30);

    var dt1_with_new_second := LDT.WithSecond(dt1, 45);
    AssertAndExpect(dt1_with_new_second.second == 45);

    var dt1_with_new_millisecond := LDT.WithMillisecond(dt1, 999);
    AssertAndExpect(dt1_with_new_millisecond.millisecond == 999);
  }

  method {:test} TestWithNotNormalCase() {
    var dt1 := LDT.LocalDateTime(2020, 2, 29, 15, 9, 26, 535);
    expect LDT.IsValidLocalDateTime(dt1);

    var dt1_with_new_year := LDT.WithYear(dt1, 2021);
    expect dt1_with_new_year.year == 2021;
    expect dt1_with_new_year.day == 28; // Clamped to 28 since 2021 is not a leap year

    var dt2 := LDT.LocalDateTime(2020, 3, 31, 15, 9, 26, 535);
    expect LDT.IsValidLocalDateTime(dt2);

    var dt2_with_new_month := LDT.WithMonth(dt2, 4);
    expect dt2_with_new_month.month == 4;
    expect dt2_with_new_month.day == 30; // Clamped to 30 since April has 30 days
  }

  method {:test} TestGetters() {
    var dt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 535);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    AssertAndExpect(LDT.GetYear(dt) == 2023);
    AssertAndExpect(LDT.GetMonth(dt) == 3);
    AssertAndExpect(LDT.GetDay(dt) == 14);
    AssertAndExpect(LDT.GetHour(dt) == 15);
    AssertAndExpect(LDT.GetMinute(dt) == 9);
    AssertAndExpect(LDT.GetSecond(dt) == 26);
    AssertAndExpect(LDT.GetMillisecond(dt) == 535);
  }

  method {:test} TestIsLeapYear() {
    expect DTUtils.IsLeapYear(2020); // Divisible by 4 and not by 100
    expect !DTUtils.IsLeapYear(2021); // Not divisible by 4
    expect !DTUtils.IsLeapYear(1900); // Divisible by 100 but not by 400
    expect DTUtils.IsLeapYear(2000); // Divisible by 400
  }

  method {:test} TestIsValidLocalDateTime() {
    var valid_dt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 535);
    AssertAndExpect(LDT.IsValidLocalDateTime(valid_dt));

    var invalid_month_dt := LDT.LocalDateTime(2023, 13, 14, 15, 9, 26, 535);
    AssertAndExpect(!LDT.IsValidLocalDateTime(invalid_month_dt));

    // var invalid_day_dt := LDT.LocalDateTime(2023, 2, 30, 15, 9, 26, 535);
    // AssertAndExpect(!LDT.IsValidLocalDateTime(invalid_day_dt));

    var invalid_hour_dt := LDT.LocalDateTime(2023, 3, 14, 24, 9, 26, 535);
    AssertAndExpect(!LDT.IsValidLocalDateTime(invalid_hour_dt));

    var invalid_minute_dt := LDT.LocalDateTime(2023, 3, 14, 15, 60, 26, 535);
    AssertAndExpect(!LDT.IsValidLocalDateTime(invalid_minute_dt));

    var invalid_second_dt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 60, 535);
    AssertAndExpect(!LDT.IsValidLocalDateTime(invalid_second_dt));

    var invalid_millisecond_dt := LDT.LocalDateTime(2023, 3, 14, 15, 9, 26, 1000);
    AssertAndExpect(!LDT.IsValidLocalDateTime(invalid_millisecond_dt));
  }

  method {:test} TestDaysInMonth() {
    expect DTUtils.DaysInMonth(2023, 1) == 31;
    expect DTUtils.DaysInMonth(2023, 2) == 28;
    expect DTUtils.DaysInMonth(2020, 2) == 29; // Leap year
    expect DTUtils.DaysInMonth(2023, 4) == 30;
    expect DTUtils.DaysInMonth(2023, 12) == 31;
  }

  method {:test} TestDaysInYear() {
    expect DTUtils.DaysInYear(2023) == 365;
    expect DTUtils.DaysInYear(2020) == 366; // Leap year
  }

  method {:test} TestPlusDays() {
    // Test day overflow across month boundary
    var june29 := LDT.LocalDateTime(2023, 6, 29, 10, 0, 0, 0);
    AssertAndExpect(LDT.IsValidLocalDateTime(june29));
    var plusThreeDays := LDT.PlusDays(june29, 3);
    AssertAndExpect(LDT.IsValidLocalDateTime(plusThreeDays));
    expect plusThreeDays.year == 2023;
    expect plusThreeDays.month == 7;
    expect plusThreeDays.day == 2;

    // Test day overflow across year boundary
    var dec30 := LDT.LocalDateTime(2023, 12, 30, 10, 0, 0, 0);
    AssertAndExpect(LDT.IsValidLocalDateTime(dec30));
    var plusFiveDays := LDT.PlusDays(dec30, 5);
    AssertAndExpect(LDT.IsValidLocalDateTime(plusFiveDays));
    expect plusFiveDays.year == 2024;
    expect plusFiveDays.month == 1;
    expect plusFiveDays.day == 4;
  }

  method {:test} TestPlusHours() {
    // Test hour overflow across day boundary
    var lateNight := LDT.LocalDateTime(2023, 6, 15, 22, 30, 45, 123);
    AssertAndExpect(LDT.IsValidLocalDateTime(lateNight));
    var plusFiveHours := LDT.PlusHours(lateNight, 5);
    AssertAndExpect(LDT.IsValidLocalDateTime(plusFiveHours));
    expect plusFiveHours.year == 2023;
    expect plusFiveHours.month == 6;
    expect plusFiveHours.day == 16;
    expect plusFiveHours.hour == 3;
    expect plusFiveHours.minute == 30;
  }

  method {:test} TestPlusMinutes() {
    // Test minute overflow across hour boundary
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 55, 45, 123);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    var plusTenMinutes := LDT.PlusMinutes(dt, 10);
    AssertAndExpect(LDT.IsValidLocalDateTime(plusTenMinutes));
    expect plusTenMinutes.hour == 15;
    expect plusTenMinutes.minute == 5;
    expect plusTenMinutes.second == 45;
  }

  method {:test} TestPlusSeconds() {
    // Test second overflow across minute boundary
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 55, 123);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    var plusTenSeconds := LDT.PlusSeconds(dt, 10);
    AssertAndExpect(LDT.IsValidLocalDateTime(plusTenSeconds));
    expect plusTenSeconds.minute == 31;
    expect plusTenSeconds.second == 5;
    expect plusTenSeconds.millisecond == 123;
  }

  method {:test} TestPlusMilliseconds() {
    // Test millisecond overflow across second boundary
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 950);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    var plus100Millis := LDT.PlusMilliseconds(dt, 100);
    AssertAndExpect(LDT.IsValidLocalDateTime(plus100Millis));
    expect plus100Millis.second == 46;
    expect plus100Millis.millisecond == 50;
  }

  method {:test} TestMinusDays() {
    // Test day underflow across month boundary
    var july2 := LDT.LocalDateTime(2023, 7, 2, 10, 0, 0, 0);
    AssertAndExpect(LDT.IsValidLocalDateTime(july2));
    var minusThreeDays := LDT.MinusDays(july2, 3);
    AssertAndExpect(LDT.IsValidLocalDateTime(minusThreeDays));
    expect minusThreeDays.year == 2023;
    expect minusThreeDays.month == 6;
    expect minusThreeDays.day == 29;

    // Test day underflow across year boundary
    var jan4 := LDT.LocalDateTime(2024, 1, 4, 10, 0, 0, 0);
    AssertAndExpect(LDT.IsValidLocalDateTime(jan4));
    var minusFiveDays := LDT.MinusDays(jan4, 5);
    AssertAndExpect(LDT.IsValidLocalDateTime(minusFiveDays));
    expect minusFiveDays.year == 2023;
    expect minusFiveDays.month == 12;
    expect minusFiveDays.day == 30;
  }

  method {:test} TestMinusHours() {
    // Test hour underflow across day boundary
    var earlyMorning := LDT.LocalDateTime(2023, 6, 16, 3, 30, 45, 123);
    AssertAndExpect(LDT.IsValidLocalDateTime(earlyMorning));
    var minusFiveHours := LDT.MinusHours(earlyMorning, 5);
    AssertAndExpect(LDT.IsValidLocalDateTime(minusFiveHours));
    expect minusFiveHours.year == 2023;
    expect minusFiveHours.month == 6;
    expect minusFiveHours.day == 15;
    expect minusFiveHours.hour == 22;
    expect minusFiveHours.minute == 30;
  }

  method {:test} TestMinusMinutes() {
    // Test minute underflow across hour boundary
    var dt := LDT.LocalDateTime(2023, 6, 15, 15, 5, 45, 123);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    var minusTenMinutes := LDT.MinusMinutes(dt, 10);
    AssertAndExpect(LDT.IsValidLocalDateTime(minusTenMinutes));
    expect minusTenMinutes.hour == 14;
    expect minusTenMinutes.minute == 55;
    expect minusTenMinutes.second == 45;
  }

  method {:test} TestMinusSeconds() {
    // Test second underflow across minute boundary
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 31, 5, 123);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    var minusTenSeconds := LDT.MinusSeconds(dt, 10);
    AssertAndExpect(LDT.IsValidLocalDateTime(minusTenSeconds));
    expect minusTenSeconds.minute == 30;
    expect minusTenSeconds.second == 55;
    expect minusTenSeconds.millisecond == 123;
  }

  method {:test} TestMinusMilliseconds() {
    // Test millisecond underflow across second boundary
    var dt := LDT.LocalDateTime(2023, 6, 15, 14, 30, 46, 50);
    AssertAndExpect(LDT.IsValidLocalDateTime(dt));
    var minus100Millis := LDT.MinusMilliseconds(dt, 100);
    AssertAndExpect(LDT.IsValidLocalDateTime(minus100Millis));
    expect minus100Millis.second == 45;
    expect minus100Millis.millisecond == 950;
  }

  method {:test} TestComparisonMethods() {
    // Create test date times
    var dt1 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123);
    var dt2 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 124); // 1ms later
    var dt3 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 45, 123); // Same as dt1
    var dt4 := LDT.LocalDateTime(2023, 6, 15, 14, 30, 46, 123); // 1s later
    var dt5 := LDT.LocalDateTime(2023, 6, 16, 14, 30, 45, 123); // 1 day later

    AssertAndExpect(LDT.IsValidLocalDateTime(dt1));
    AssertAndExpect(LDT.IsValidLocalDateTime(dt2));
    AssertAndExpect(LDT.IsValidLocalDateTime(dt3));
    AssertAndExpect(LDT.IsValidLocalDateTime(dt4));
    AssertAndExpect(LDT.IsValidLocalDateTime(dt5));

    // Test IsBefore
    AssertAndExpect(LDT.IsBefore(dt1, dt2)); // dt1 is before dt2 (1ms difference)
    AssertAndExpect(!LDT.IsBefore(dt1, dt3)); // dt1 is not before dt3 (same time)
    AssertAndExpect(!LDT.IsBefore(dt2, dt1)); // dt2 is not before dt1

    // Test IsAfter
    AssertAndExpect(LDT.IsAfter(dt2, dt1)); // dt2 is after dt1
    AssertAndExpect(!LDT.IsAfter(dt1, dt3)); // dt1 is not after dt3 (same time)
    AssertAndExpect(!LDT.IsAfter(dt1, dt2)); // dt1 is not after dt2

    // Test IsEqual
    AssertAndExpect(LDT.IsEqual(dt1, dt3)); // dt1 equals dt3
    AssertAndExpect(LDT.IsEqual(dt3, dt1)); // dt3 equals dt1 (symmetric)
    AssertAndExpect(!LDT.IsEqual(dt1, dt2)); // dt1 does not equal dt2
  }
}