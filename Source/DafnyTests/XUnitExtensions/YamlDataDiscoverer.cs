using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using DafnyTests;
using Xunit.Abstractions;
using Xunit.Sdk;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NodeDeserializers;
using YamlDotNet.Serialization.ObjectFactories;
using YamlDotNet.Serialization.Utilities;

namespace XUnitExtensions {
  public class YamlDataDiscoverer : IDataDiscoverer {
    public virtual IParser GetYamlParser(Stream stream)  {
      return new Parser(new StreamReader(stream));
    }

    public virtual IDeserializer GetDeserializer() {
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
    
    private IEnumerable<object[]> ResourceData(IDeserializer deserializer, MethodInfo testMethod, string resourceName, bool withParameterNames) {
      Stream stream = testMethod.DeclaringType.Assembly.GetManifestResourceStream(resourceName);
      IParser parser = GetYamlParser(stream);
      parser.Consume<StreamStart>();
      parser.Consume<DocumentStart>();
            
      if (withParameterNames) {
        IObjectFactory argumentsFactory = new DefaultObjectFactory();
        INodeDeserializer collectionDeserializer = new CollectionNodeDeserializer(argumentsFactory);
        var nestedObjectDeserializer = ForMethodInfoDeserializeFn(deserializer, testMethod, resourceName);
        if (collectionDeserializer.Deserialize(parser, typeof(List<MethodArguments>), nestedObjectDeserializer, out var value)) {
          List<MethodArguments> argumentses = (List<MethodArguments>) value;
          return argumentses.SelectMany(a => a.Combinations());
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
          results.Select(value => new[]{ new SourceFile(resourceName), value }) : 
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
      bool withParameterNames = (bool)attributeArgs[0];

      string resourceNamePrefix = methodInfo.DeclaringType.FullName + "." + methodInfo.Name;
//      throw new ArgumentException(resourceNamePrefix);
      return methodInfo.DeclaringType.Assembly.GetManifestResourceNames()
        .Where(n => n.StartsWith(resourceNamePrefix))
        .SelectMany(path => ResourceData(deserializer, methodInfo, path, withParameterNames));
    }
  }

  public class MethodArguments : IYamlConvertible {

    private MethodInfo Method;
    private Dictionary<string, int> ParameterNameIndexes;
    private object[] Arguments;

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
        ParameterInfo parameter = Method.GetParameters()[parameterIndex];
        Type parameterType = parameter.ParameterType;
        ForEachAttribute forEach = parameter.GetCustomAttribute<ForEachAttribute>();
        if (forEach != null) {
          parameterType = forEach.EnumerableTypeOf(parameterType);
        }
        
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

    public IEnumerable<object[]> Combinations() {
      // TODO: Optimize this away when there are no ForEach attributes
      IEnumerable<IEnumerable<object>> lifted = Arguments.Select((arg, index) => {
        ParameterInfo parameter = Method.GetParameters()[index];
        ForEachAttribute forEach = parameter.GetCustomAttribute<ForEachAttribute>();
        return forEach == null ? new[] {arg} : ((IEnumerable)arg).Cast<object>();
      });
      return lifted.CartesianProduct().Select(e => e.ToArray());
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
