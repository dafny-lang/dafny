using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;

namespace DafnyTests {
  public class YamlUtils {
        
    public static IEnumerable<YamlNode> Expand(YamlNode node) {
      if (node is YamlSequenceNode seqNode) {
        return seqNode.SelectMany(child => Expand(child));
      } else if (node is YamlMappingNode mappingNode) {
        return mappingNode.Select(ExpandValue).CartesianProduct().Select(FromPairs);
      } else {
        return new[] {node};
      }
    }

    private static IEnumerable<KeyValuePair<YamlNode, YamlNode>> ExpandValue(KeyValuePair<YamlNode, YamlNode> pair) {
      return Expand(pair.Value).Select(v => new KeyValuePair<YamlNode, YamlNode>(pair.Key, v));
    }

    private static YamlMappingNode FromPairs(IEnumerable<KeyValuePair<YamlNode, YamlNode>> pairs) {
      var result = new YamlMappingNode();
      foreach (var pair in pairs) {
        result.Add(pair.Key, pair.Value);
      }

      return result;
    }
        
    [Theory]
    [InlineData("multiple.yml", "multiple.expect.yml")]
    public void ExpandTest(string inputPath, string expectedOutputPath) {
      string fullInputPath = "./YamlTests/" + inputPath;
      string fullExpectedOutputPath = "./YamlTests/" + expectedOutputPath;

      using (var reader = File.OpenText(fullInputPath)) {
        var yamlStream = new YamlStream();
        yamlStream.Load(reader);
        var root = yamlStream.Documents[0].RootNode;
        var expanded = Expand(root);

        var outputWriter = new StringWriter();
        var serializer = new SerializerBuilder().Build();
        serializer.Serialize(outputWriter, expanded);
        string expectedOutput = File.ReadAllText(fullExpectedOutputPath);
        Assert.Equal(expectedOutput, outputWriter.ToString());
      }
    }

    [Theory]
    [YamlFileData("YamlTests/calculator.yml")]
    public void CalculatorTest(int lhs, int rhs, int expected) {
      Assert.Equal(expected, lhs + rhs);
    }
    
    [Theory]
    [YamlFileData("YamlTests/calculator-combinatorial.yml")]
    public void CalculatorCombinatorialTest([ForEach()] int lhs, [ForEach()] int rhs) {
      Assert.Equal(rhs + lhs, lhs + rhs);
    }
    
    [Theory]
    [YamlFileData("YamlTests/configs.yml", withParameterNames: false)]
    public void DictionaryTest(ISourceInformation source, Dictionary<string, string> config) {
      Assert.Equal(3, config.Count);
    }

    public class ExpandList<T> : List<T> {
      
    }

    [DataDiscoverer("DafnyTests.CustomDiscoverer", "DafnyTests")]
    public class CustomYamlFileDataAttribute : YamlFileDataAttribute {
      public CustomYamlFileDataAttribute(string rootPath, bool withParameterNames = true) : base(rootPath, withParameterNames) {
      }
    }
    
    [Theory]
    [CustomYamlFileData("YamlTests/calculator-tagged.yml")]
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

  public class CustomDiscoverer : YamlFileDataDiscoverer {
    public override IDeserializer GetDeserializer() {
      return new DeserializerBuilder().WithTagMapping("!range", typeof(Range))
        .WithNamingConvention(CamelCaseNamingConvention.Instance).Build();
    }
  }
}