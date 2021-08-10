using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;

namespace DafnyDriver.Test.XUnitExtensions {
  public class YamlDataTests {

    private void AssertTheoryData(string methodName, IEnumerable<object> expectedData) {
      var method = typeof(YamlDataTests).GetMethod(methodName);
      var attribute = (YamlDataAttribute)Attribute.GetCustomAttribute(method!, typeof(YamlDataAttribute));
      var discoverer = new YamlDataDiscoverer();
      Assert.Equal(expectedData, discoverer.GetData(method, attribute!.WithParameterNames));
    }
    
    [Theory]
    [YamlData()]
    public void CalculatorTest(int lhs, int rhs, int expected) {
      Assert.Equal(expected, lhs + rhs);
    }

    [Fact]
    public void CalculatorTestData() {
      AssertTheoryData(nameof(CalculatorTest), new [] {
        new object[]{ 2, 2, 4 },
        new object[]{ 3, 4, 7 }
      });
    }
    
    [Theory]
    [YamlData()]
    public void CalculatorCombinatorialTest([ForEach()] int lhs, [ForEach()] int rhs) {
      Assert.Equal(rhs + lhs, lhs + rhs);
    }
    
    [Fact]
    public void CalculatorCombinatorialTestData() {
      AssertTheoryData(nameof(CalculatorCombinatorialTest), new [] {
        new object[]{ 1, 5 },
        new object[]{ 1, 10 },
        new object[]{ 2, 5 },
        new object[]{ 2, 10 },
        new object[]{ 3, 5 },
        new object[]{ 3, 10 },
        new object[]{ 4, 5 },
        new object[]{ 4, 10 },
        new object[]{ 5, 5 },
        new object[]{ 5, 10 },
      });
    }
    
    [Theory]
    [YamlData()]
    public void MultiFileTest(int a, int b) {
      Assert.Equal(a + 1, b);
    }
    
    [Fact]
    public void MultiFileTestData() {
      AssertTheoryData(nameof(MultiFileTest), new [] {
        new object[]{ 1, 2 },
        new object[]{ 3, 4 },
        new object[]{ 5, 6 },
        new object[]{ 7, 8 },
      });
    }

    [Theory]
    [YamlData(false)]
    public void DictionaryTest(Dictionary<string, string> config) {
      Assert.Equal(3, config.Count);
    }
    
    [Fact]
    public void DictionaryTestData() {
      AssertTheoryData(nameof(DictionaryTest), new [] {
        new object[]{ new Dictionary<string, object> {
          ["one"] = "1",
          ["two"] = "2",
          ["three"] = "3"
        }},
        new object[]{ new Dictionary<string, object> {
          ["four"] = "4",
          ["five"] = "5",
          ["six"] = "6"
        }}
      });
    }

    [DataDiscoverer("DafnyDriver.Test.XUnitExtensions.CustomDiscoverer", "DafnyDriver.Test")]
    public class CustomYamlDataAttribute : YamlDataAttribute {
      public CustomYamlDataAttribute(bool withParameterNames = true) : base(withParameterNames) {
      }
    }
    
    [Theory]
    [CustomYamlData()]
    public void CustomDataDiscovererTest([ForEach()] int lhs, [ForEach()] int rhs) {
      Assert.Equal(rhs + lhs, lhs + rhs);
    }
    
    [Fact]
    public void CustomDataDiscovererTestData() {
      AssertTheoryData(nameof(CustomDataDiscovererTest), new [] {
        new object[]{ 0, 0 },
        new object[]{ 0, 1 },
        new object[]{ 1, 0 },
        new object[]{ 1, 1 },
        new object[]{ 2, 0 },
        new object[]{ 2, 1 },
        new object[]{ 3, 0 },
        new object[]{ 3, 1 },
        new object[]{ 4, 0 },
        new object[]{ 4, 1 },
      });
    }
  }
  
  public class Range : IEnumerable<int> {

    public int Start;
    public int End;

    public IEnumerator<int> GetEnumerator() {
      return Enumerable.Range(Start, End).GetEnumerator();
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }
  }

  public class CustomDiscoverer : YamlDataDiscoverer {
    public override IDeserializer GetDeserializer(string manifestResourceName) {
      return new DeserializerBuilder().WithTagMapping("!range", typeof(Range))
        .WithNamingConvention(CamelCaseNamingConvention.Instance).Build();
    }
  }
}