using System.CommandLine;
using System.Globalization;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class CoresOptionTest {
  private static (uint Cores, string? Error) ParseCores(string value, string culture) {
    var ambient = CultureInfo.CurrentCulture;
    CultureInfo.CurrentCulture = new CultureInfo(culture);
    try {
      var result = BoogieOptionBag.Cores.Parse(["--cores", value]);
      return result.Errors.Count == 0
        ? (result.GetValueForOption(BoogieOptionBag.Cores), null)
        : (0, result.Errors[0].Message);
    }
    finally {
      CultureInfo.CurrentCulture = ambient;
    }
  }

  // Under de-DE "." groups digits, under fr-FR it is no separator at all, and under ar "+" is no sign.
  [Theory]
  [InlineData("50.5%", "de-DE")]
  [InlineData("50.5%", "fr-FR")]
  [InlineData("+5", "ar")]
  public void ValueIgnoresTheAmbientCulture(string value, string culture) {
    var invariant = ParseCores(value, CultureInfo.InvariantCulture.Name);
    Assert.Null(invariant.Error);
    Assert.Equal(invariant, ParseCores(value, culture));
  }

  [Theory]
  [InlineData("50,5%")]
  [InlineData("NaN%")]
  [InlineData("Infinity%")]
  [InlineData("-50%")]
  [InlineData("2147483648")]
  public void InvalidValueIsRejected(string value) {
    Assert.NotNull(ParseCores(value, CultureInfo.InvariantCulture.Name).Error);
  }

  // More cores than int.MaxValue, but fewer than uint.MaxValue, on any machine.
  [Fact]
  public void PercentageBeyondIntMaxValueCoresIsRejected() {
    var percentage = (1.5 * int.MaxValue / Environment.ProcessorCount * 100).ToString(CultureInfo.InvariantCulture);
    Assert.NotNull(ParseCores($"{percentage}%", CultureInfo.InvariantCulture.Name).Error);
  }
}
