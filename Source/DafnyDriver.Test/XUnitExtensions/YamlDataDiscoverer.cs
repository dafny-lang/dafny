using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using JetBrains.Annotations;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NodeDeserializers;
using YamlDotNet.Serialization.ObjectFactories;
using YamlDotNet.Serialization.Utilities;

namespace DafnyDriver.Test.XUnitExtensions {
  public class YamlDataDiscoverer : FileDataDiscoverer {
    public virtual IParser GetYamlParser(string fileName, Stream stream) {
      return new Parser(new StreamReader(stream));
    }

    public virtual IDeserializer GetDeserializer(string fileName) {
      return new Deserializer();
    }

    private static Func<IParser, Type, object> ForMethodInfoDeserializeFn(IDeserializer deserializer, MethodInfo testMethod) {
      return (parser, type) => {
        if (type == typeof(MethodArguments)) {
          MethodArguments arguments = new MethodArguments(testMethod);
          arguments.Read(parser, type, t => deserializer.Deserialize(parser, t));
          return arguments;
        } else {
          return deserializer.Deserialize(parser, type);
        }
      };
    }
    
    public override bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }
    
    protected override IEnumerable<object[]> FileData(IAttributeInfo dataAttribute, IMethodInfo testMethod, string fileName) {
      var withParameterNames = dataAttribute.GetNamedArgument<bool>(nameof(YamlDataAttribute.WithParameterNames));
      // YamlDotNet's deserialization framework requires runtime type information
      MethodInfo methodInfo = testMethod.ToRuntimeMethod();
      if (methodInfo == null) {
        return null;
      }
      
      try {
        using Stream stream = File.OpenRead(fileName);
        IParser parser = GetYamlParser(fileName, stream);
        if (parser == null) { 
          return Enumerable.Empty<object[]>();
        }

        IDeserializer deserializer = GetDeserializer(fileName);
        parser.Consume<StreamStart>();
        parser.Consume<DocumentStart>();

        if (withParameterNames) {
          IObjectFactory argumentsFactory = new DefaultObjectFactory();
          INodeDeserializer collectionDeserializer = new CollectionNodeDeserializer(argumentsFactory);
          var nestedObjectDeserializer = ForMethodInfoDeserializeFn(deserializer, methodInfo);
          if (collectionDeserializer.Deserialize(parser, typeof(List<MethodArguments>), nestedObjectDeserializer,
            out var value)) {
            List<MethodArguments> argumentses = (List<MethodArguments>) value;
            return argumentses.SelectMany(a => a.Combinations());
          } else {
            throw new ArgumentException();
          }
        } else {
          IEnumerable<ParameterInfo> parameters = methodInfo.GetParameters();
          Type targetType = typeof(IEnumerable<>).MakeGenericType(parameters.Single().ParameterType);
          IEnumerable<object> results = (IEnumerable<object>) deserializer.Deserialize(parser, targetType);
          return results.Select(value => new[] {value});
        }
      } catch (Exception e) {
        throw new ArgumentException(
          "Exception thrown while trying to deserialize test data from file: " + fileName, e);
      }
    }
  }

  public class MethodArguments : IYamlConvertible {

    private MethodInfo Method;
    private Dictionary<string, int> ParameterNameIndexes;
    private object[] Arguments;

    public MethodArguments(MethodInfo methodInfo) {
      Method = methodInfo;
      Arguments = new object[Method.GetParameters().Length];
      ParameterNameIndexes = Method.GetParameters()
        .Select((value, index) => new KeyValuePair<string, int>(value.Name, index))
        .ToDictionary(p => p.Key, p => p.Value);
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
}
