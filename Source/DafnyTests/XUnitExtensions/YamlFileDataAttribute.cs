using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using DafnyTests;
using Xunit.Sdk;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;

namespace XUnitExtensions {
  public class YamlFileDataAttribute : DataAttribute {

    private string RootPath;
    private bool WithParameterNames;
    private bool WithSourceFile;
    private IDeserializer Deserializer = new DeserializerBuilder().Build();

    public YamlFileDataAttribute(string rootPath, bool withParameterNames = true, bool withSourceFile = false) {
      RootPath = rootPath;
      WithParameterNames = withParameterNames;
      WithSourceFile = withSourceFile;
    }

    private class ParsingEventBuffer : IEmitter {
      public List<ParsingEvent> ParsingEvents = new List<ParsingEvent>();

      public void Emit(ParsingEvent parsingEvent) {
        ParsingEvents.Add(parsingEvent);
      }
    }
    
    private class ParsingEventListParser : IParser {
      private readonly IEnumerator<ParsingEvent> Enumerator;

      public ParsingEventListParser(IEnumerator<ParsingEvent> enumerator) {
        Enumerator = enumerator;
      }
     
      public bool MoveNext() {
        return Enumerator.MoveNext();
      }

      public ParsingEvent Current => Enumerator.Current; 
    }
    
    private IParser NodeParser(YamlNode node) {
      ParsingEventBuffer buffer = new ParsingEventBuffer();
      YamlDocument doc = new YamlDocument(node);
      YamlStream stream = new YamlStream();
      stream.Add(doc);
      stream.Save(buffer, false);
      return new ParsingEventListParser(buffer.ParsingEvents.GetEnumerator());
    }

    private object DeserializeParameter(ParameterInfo parameterInfo, YamlNode mappingNode) {
      return Deserializer.Deserialize(NodeParser(mappingNode), parameterInfo.ParameterType);
    }
    
    private IEnumerable<object> MethodArguments(MethodInfo testMethod, string path, YamlMappingNode mappingNode) {
      IEnumerable<object> result;
      IEnumerable<ParameterInfo> parameters = testMethod.GetParameters();
      if (WithSourceFile) {
        parameters = parameters.Skip(1);
      } 
      if (WithParameterNames) {
        result = parameters.Select(param => DeserializeParameter(param, mappingNode[param.Name])).ToArray();
      } else {
        result = new[] {DeserializeParameter(parameters.Single(), mappingNode)};
      }

      return WithSourceFile ? new[] {path}.Concat(result) : result;
    }
    
    private IEnumerable<object[]> FileData(MethodInfo testMethod, string path) {
      var yamlStream = new YamlStream();
      yamlStream.Load(new StreamReader(path));
      // TODO: error checking and expansion
      YamlSequenceNode node = (YamlSequenceNode)yamlStream.Documents[0].RootNode;
      return node.Select(childNode => MethodArguments(testMethod, path, (YamlMappingNode)childNode).ToArray());
    }
    
    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      if (RootPath.EndsWith(".yml")) {
        return FileData(testMethod, RootPath);
      } else {
        var filePaths = Directory.GetFiles(RootPath, "*.yml", SearchOption.AllDirectories)
                                 .Select(path => Path.GetRelativePath(RootPath, path));
        return filePaths.SelectMany(path => FileData(testMethod, path));
      }
    }
  }
}