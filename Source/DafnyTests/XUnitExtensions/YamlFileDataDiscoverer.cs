using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Xunit.Abstractions;
using Xunit.Sdk;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;

namespace XUnitExtensions {
  public class YamlFileDataDiscoverer : IDataDiscoverer {
    public IParser GetYamlParser(string filePath)  {
      return new Parser(new StreamReader(filePath));
    }

    public IDeserializer GetDeserializer() {
      return new Deserializer();
    }

    public bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
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

    private object DeserializeParameter(IDeserializer deserializer, ParameterInfo parameterInfo, YamlNode mappingNode) {
      return deserializer.Deserialize(NodeParser(mappingNode), parameterInfo.ParameterType);
    }
    
    private IEnumerable<object> MethodArguments(IDeserializer deserializer, MethodInfo testMethod, string path, bool withParameterNames, YamlMappingNode mappingNode) {
      IEnumerable<object> result;
      IEnumerable<ParameterInfo> parameters = testMethod.GetParameters();
      bool withSourceFile = parameters.First().ParameterType.Equals(typeof(ISourceInformation));
      if (withSourceFile) {
        parameters = parameters.Skip(1);
      }
      if (withParameterNames) {
        result = parameters.Select(param => DeserializeParameter(deserializer, param, mappingNode[param.Name])).ToArray();
      } else {
        result = new[] {DeserializeParameter(deserializer, parameters.Single(), mappingNode)};
      }

      return withSourceFile ? new[] {new SourceFile(path)}.Concat(result) : result;
    }
    
    private IEnumerable<object[]> FileData(IDeserializer deserializer, MethodInfo testMethod, string path, bool withParameterNames) {
      var yamlStream = new YamlStream();
      yamlStream.Load(new StreamReader(path));
      // TODO: error checking and expansion
      YamlSequenceNode node = (YamlSequenceNode)yamlStream.Documents[0].RootNode;
      return node.Select(childNode => MethodArguments(deserializer, testMethod, path, withParameterNames, (YamlMappingNode)childNode).ToArray());
    }

    public IEnumerable<object[]> GetData(IAttributeInfo attributeInfo, IMethodInfo testMethod) {
      // YamlDotNet's deserialization framework requires runtime type information
      MethodInfo methodInfo = testMethod.ToRuntimeMethod();
      if (methodInfo == null) {
        return null;
      }
      
      IDeserializer deserializer = GetDeserializer();

      List<object> attributeArgs = attributeInfo.GetConstructorArguments().ToList();
      string rootPath = (string)attributeArgs[0];
      bool withParameterNames = (bool)attributeArgs[1];
      
      if (rootPath.EndsWith(".yml")) {
        return FileData(deserializer, methodInfo, rootPath, withParameterNames);
      } else {
        var filePaths = Directory.GetFiles(rootPath, "*.yml", SearchOption.AllDirectories)
                                 .Select(path => Path.GetRelativePath(rootPath, path));
        return filePaths.SelectMany(path => FileData(deserializer, methodInfo, path, withParameterNames));
      }
    }
  }
  
  public class SourceFile : SourceInformation {

    public SourceFile() {
      
    }
    
    public SourceFile(string fileName) {
      FileName = fileName;
    }

    public override string ToString() {
      return FileName;
    }
  }
}
