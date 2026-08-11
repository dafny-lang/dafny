using System;
using System.CommandLine;
using System.Globalization;
using System.Threading;
using Microsoft.Dafny;
using Xunit;

namespace DafnyCore.Test;

public class CoresOptionCultureTest {

  /// <summary>
  /// Parses "--cores &lt;value&gt;" with "culture" as the ambient culture, returning the resulting core
  /// count and any parse error. The culture is set on a thread this test owns: it has to be set
  /// somewhere, but xunit runs test classes in parallel on pool threads it reuses, so mutating the
  /// caller's culture could be observed by a concurrently running test.
  /// </summary>
  private static (uint Cores, string? Error) ParseCores(string value, string culture) {
    uint cores = 0;
    string? error = null;
    Exception? failure = null;
    var thread = new Thread(() => {
      CultureInfo.CurrentCulture = new CultureInfo(culture);
      try {
        var command = new Command("test") { BoogieOptionBag.Cores };
        var parsed = command.Parse(["test", "--cores", value]);
        error = parsed.Errors.Count == 0 ? null : parsed.Errors[0].Message;
        if (error == null) {
          cores = parsed.GetValueForOption(BoogieOptionBag.Cores);
        }
      } catch (Exception e) {
        failure = e;
      }
    });
    thread.Start();
    Assert.True(thread.Join(60_000), "parsing did not finish");
    Assert.Null(failure);
    return (cores, error);
  }

  /// <summary>
  /// A command-line value is not written in the ambient locale's number format. Parsing "50.5%" with
  /// the ambient separators is silently wrong under a culture where "." groups digits: it yields
  /// 505%, asking for five times the machine's cores.
  /// </summary>
  [Theory]
  [InlineData("en-US")]
  [InlineData("de-DE")]
  public void PercentageIsParsedInvariantlyAcrossCultures(string culture) {
    // Not asserting an absolute core count: that would restate the percentage-to-cores formula, and
    // the point here is only that the ambient culture does not change how the number is read.
    // "50.5%" and "50%" round to the same count at every processor count, whereas reading "50.5"
    // with "." as a group separator gives 505%, an order of magnitude more.
    var whole = ParseCores("50%", culture);
    var fractional = ParseCores("50.5%", culture);
    Assert.Null(whole.Error);
    Assert.Null(fractional.Error);
    Assert.Equal(whole.Cores, fractional.Cores);
    Assert.Equal(ParseCores("50%", "en-US").Cores, whole.Cores);
  }

  [Theory]
  [InlineData("en-US")]
  [InlineData("de-DE")]
  public void ThousandsSeparatorIsRejectedRatherThanGuessed(string culture) {
    // "1,000" means 1 under a comma-decimal culture and 1000 under a comma-grouping one, so on a
    // command line it is ambiguous and NumberStyles.Float rejects it.
    Assert.Contains("Could not parse percentage", ParseCores("1,000%", culture).Error);
  }

  /// <summary>
  /// NumberStyles.Float accepts "NaN" and "Infinity", and casting either to uint is unchecked, so
  /// they would silently become 1 core and uint.MaxValue cores respectively. A finite value whose
  /// product exceeds uint is rejected for the same reason: the cast would wrap rather than report.
  /// </summary>
  [Theory]
  [InlineData("NaN%")]
  [InlineData("Infinity%")]
  [InlineData("1e30%")]
  public void NonFiniteOrUnrepresentablePercentageIsRejected(string value) {
    Assert.Contains("does not denote a usable number of cores", ParseCores(value, "en-US").Error);
  }
}
