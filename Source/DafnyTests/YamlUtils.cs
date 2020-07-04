using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit;
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
    }
}