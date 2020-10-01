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
    private IDeserializer Deserializer = new DeserializerBuilder().Build();

    public YamlFileDataAttribute(string rootPath) {
      RootPath = rootPath;
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
    
    private object[] MethodArguments(MethodInfo testMethod, YamlMappingNode mappingNode) {
      return testMethod.GetParameters().Select(param => DeserializeParameter(param, mappingNode[param.Name])).ToArray();
    }
    
    private IEnumerable<object[]> FileData(MethodInfo testMethod, string path) {
      var yamlStream = new YamlStream();
      yamlStream.Load(new StreamReader(path));
      // TODO: error checking and expansion
      YamlSequenceNode node = (YamlSequenceNode)yamlStream.Documents[0].RootNode;
      return node.Select(childNode => MethodArguments(testMethod, (YamlMappingNode)childNode));
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