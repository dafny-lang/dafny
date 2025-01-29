using System;
using Microsoft.Dafny.LanguageServer.Language;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit;

public class ByteArrayEqualityTest {
  [Fact]
  public void EqualsMethod() {
    var oneToSeven = new byte[] { 0, 1, 2, 3, 4, 5, 6, 7 };
    var twoIsThree = new byte[] { 0, 1, 3, 3, 4, 5, 6, 7 };
    var oneToSevenAgain = new byte[] { 0, 1, 2, 3, 4, 5, 6, 7 };
    var equality = new HashEquality();
    Assert.False(equality.Equals(twoIsThree, oneToSeven));
    Assert.True(equality.Equals(oneToSevenAgain, oneToSeven));
  }

  [Fact]
  public void TestHashCode() {
    var equality = new HashEquality();
    var hashCodeOne = equality.GetHashCode([1, 0, 0, 0, 1, 1]);
    Assert.Equal(1, hashCodeOne);

    var hashCode2Power24 = equality.GetHashCode([0, 0, 0, 1, 1, 1, 1]);
    Assert.Equal(Math.Pow(2, 24), hashCode2Power24);
  }
}