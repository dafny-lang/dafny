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
  }
}