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

namespace DafnyTests.XUnitExtensions {
  public class YamlDataTests {
        
    [Theory]
    [YamlData()]
    public void CalculatorTest(int lhs, int rhs, int expected) {
      Assert.Equal(expected, lhs + rhs);
    }
    
    [Theory]
    [YamlData()]
    public void CalculatorCombinatorialTest([ForEach()] int lhs, [ForEach()] int rhs) {
      Assert.Equal(rhs + lhs, lhs + rhs);
    }
    
    [Theory]
    [YamlData(false)]
    public void DictionaryTest(Dictionary<string, string> config) {
      Assert.Equal(3, config.Count);
    }

    [DataDiscoverer("DafnyTests.XUnitExtensions.CustomDiscoverer", "DafnyTests")]
    public class CustomYamlDataAttribute : YamlDataAttribute {
      public CustomYamlDataAttribute(bool withParameterNames = true) : base(withParameterNames) {
      }
    }
    
    [Theory]
    [CustomYamlData()]
    public void CustomDataDiscovererTest([ForEach()] int lhs, [ForEach()] int rhs) {
      Assert.Equal(rhs + lhs, lhs + rhs);
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