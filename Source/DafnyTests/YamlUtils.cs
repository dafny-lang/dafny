using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;

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
    [YamlFileData("YamlTests/configs.yml", withParameterNames: false, withSourceFile: true)]
    public void DictionaryTest(string path, Dictionary<string, string> config) {
      Assert.Equal(3, config.Count);
    }

    private class MyConfigTypeConvertor : IYamlTypeConverter {
      
      public bool Accepts(Type type) {
        return type == typeof (MyConfig);
      }

      public object ReadYaml(IParser parser, Type type) {
        Dictionary<string, string> config = new Deserializer().Deserialize<Dictionary<string, string>>(parser);
        return new MyConfig(config);
      }

      public void WriteYaml(IEmitter emitter, object value, Type type) {
        throw new NotImplementedException();
      }
    }
    
    private static readonly IDeserializer DESERIALIZER = new DeserializerBuilder()
      .WithTypeConverter(new MyConfigTypeConvertor())
      .Build();
    
    public class MyConfig {

      public MyConfig(Dictionary<string, string> config) {
        Config = config;
      }
      
      private Dictionary<string, string> Config;

      public override string ToString() {
        return "<opaque>";
      }
    }
    
  }
}