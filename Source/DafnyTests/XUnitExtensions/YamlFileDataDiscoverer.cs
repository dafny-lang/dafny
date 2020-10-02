using System;
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
using YamlDotNet.Serialization.NodeDeserializers;
using YamlDotNet.Serialization.ObjectFactories;
using YamlDotNet.Serialization.Utilities;

namespace XUnitExtensions {
  public class YamlFileDataDiscoverer : IDataDiscoverer {
    public IParser GetYamlParser(string filePath)  {
      return new Parser(new StreamReader(filePath));
    }

    public IDeserializer GetDeserializer() {
      return new Deserializer();
    }

    private Func<IParser, Type, object> ForMethodInfoDeserializeFn(IDeserializer deserializer, MethodInfo testMethod, string path) {
      return (parser, type) => {
        if (type == typeof(MethodArguments)) {
          MethodArguments arguments = new MethodArguments(testMethod, path);
          arguments.Read(parser, type, t => deserializer.Deserialize(parser, t));
          return arguments;
        } else {
          return deserializer.Deserialize(parser, type);
        }
      };
    }
    
    public bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }
    private IEnumerable<object[]> FileData(IDeserializer deserializer, MethodInfo testMethod, string path, bool withParameterNames) {
      IParser parser = GetYamlParser(path);
      parser.Consume<StreamStart>();
      parser.Consume<DocumentStart>();
            
      if (withParameterNames) {
        IObjectFactory argumentsFactory = new DefaultObjectFactory();
        INodeDeserializer collectionDeserializer = new CollectionNodeDeserializer(argumentsFactory);
        if (collectionDeserializer.Deserialize(parser, typeof(List<MethodArguments>), ForMethodInfoDeserializeFn(deserializer, testMethod, path), out var value)) {
          List<MethodArguments> argumentses = (List<MethodArguments>) value;
          return argumentses.Select(a => a.Arguments);
        } else {
          throw new ArgumentException();
        }
      } else {
        IEnumerable<ParameterInfo> parameters = testMethod.GetParameters();
        bool withSourceFile = parameters.First().ParameterType.Equals(typeof(ISourceInformation));
        if (withSourceFile) {
          parameters = parameters.Skip(1);
        }
        IEnumerable<object> results = (IEnumerable<object>)deserializer.Deserialize(parser, typeof(List<>).MakeGenericType(parameters.Single().ParameterType));
        
        return withSourceFile ? 
          results.Select(value => new[]{ new SourceFile(path), value }) : 
          results.Select(value => new[]{ value });
      }
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

  public class MethodArguments : IYamlConvertible {

    private MethodInfo Method;
    private Dictionary<string, int> ParameterNameIndexes;
    public object[] Arguments { get; }

    public MethodArguments(MethodInfo methodInfo, string path) {
      Method = methodInfo;
      Arguments = new object[Method.GetParameters().Length];
      ParameterNameIndexes = Method.GetParameters()
        .Select((value, index) => new KeyValuePair<string, int>(value.Name, index))
        .ToDictionary(p => p.Key, p => p.Value);
      var sourceFileParameter = Method.GetParameters().FirstOrDefault(p => p.ParameterType.Equals(typeof(ISourceInformation)));
      if (sourceFileParameter != null) {
        Arguments[ParameterNameIndexes[sourceFileParameter.Name]] = new SourceFile(path);
      }
    }
    
    public void Read(IParser parser, Type expectedType, ObjectDeserializer nestedObjectDeserializer) {
      if (!parser.TryConsume(out MappingStart _)) {
        throw new ArgumentException();
      }
      while (!parser.TryConsume(out MappingEnd _)) {
        Scalar scalar = parser.Consume<Scalar>();
        int parameterIndex = ParameterNameIndexes[scalar.Value];
        Type parameterType = Method.GetParameters()[parameterIndex].ParameterType;
        
        object argument = nestedObjectDeserializer(parameterType);
        IValuePromise valuePromise = argument as IValuePromise;
        if (valuePromise != null) {
          valuePromise.ValueAvailable += (Action<object>) (v => Arguments[parameterIndex] = TypeConverter.ChangeType(v, parameterType));
        } else {
          Arguments[parameterIndex] = TypeConverter.ChangeType(argument, parameterType);
        }
      }
    }

    public void Write(IEmitter emitter, ObjectSerializer nestedObjectSerializer) {
      throw new NotImplementedException();
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
