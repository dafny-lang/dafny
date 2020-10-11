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
    public virtual IParser GetYamlParser(string manifestResourceName, Stream stream)  {
      return new Parser(new StreamReader(stream));
    }

    public virtual IDeserializer GetDeserializer(string manifestResourceName) {
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
    
    public bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }
    
    private IEnumerable<object[]> ResourceData(MethodInfo testMethod, string resourceName, bool withParameterNames) {
      try {
        using Stream stream = testMethod.DeclaringType.Assembly.GetManifestResourceStream(resourceName);
        IParser parser = GetYamlParser(resourceName, stream);
        if (parser == null) {
          return Enumerable.Empty<object[]>();
        }

        IDeserializer deserializer = GetDeserializer(resourceName);
        parser.Consume<StreamStart>();
        parser.Consume<DocumentStart>();

        if (withParameterNames) {
          IObjectFactory argumentsFactory = new DefaultObjectFactory();
          INodeDeserializer collectionDeserializer = new CollectionNodeDeserializer(argumentsFactory);
          var nestedObjectDeserializer = ForMethodInfoDeserializeFn(deserializer, testMethod);
          if (collectionDeserializer.Deserialize(parser, typeof(List<MethodArguments>), nestedObjectDeserializer,
            out var value)) {
            List<MethodArguments> argumentses = (List<MethodArguments>) value;
            return argumentses.SelectMany(a => a.Combinations());
          } else {
            throw new ArgumentException();
          }
        } else {
          IEnumerable<ParameterInfo> parameters = testMethod.GetParameters();
          Type targetType = typeof(IEnumerable<>).MakeGenericType(parameters.Single().ParameterType);
          IEnumerable<object> results = (IEnumerable<object>) deserializer.Deserialize(parser, targetType);
          return results.Select(value => new[] {value});
        }
      } catch (Exception e) {
        throw new ArgumentException(
          "Exception thrown while trying to deserialize test data from manifest resource: " + resourceName, e);
      }
    }

    public IEnumerable<object[]> GetData(IAttributeInfo attributeInfo, IMethodInfo testMethod) {
      // YamlDotNet's deserialization framework requires runtime type information
      MethodInfo methodInfo = testMethod.ToRuntimeMethod();
      if (methodInfo == null) {
        return null;
      }

      List<object> attributeArgs = attributeInfo.GetConstructorArguments().ToList();
      bool withParameterNames = (bool) attributeArgs[0];

      return GetData(methodInfo, withParameterNames);
    }

    public IEnumerable<object[]> GetData(MethodInfo methodInfo, bool withParameterNames) {
      string resourceNamePrefix = methodInfo.DeclaringType.FullName + "." + methodInfo.Name;
      IEnumerable<object[]> result = methodInfo.DeclaringType.Assembly.GetManifestResourceNames()
        .Where(n => n.StartsWith(resourceNamePrefix))
        .SelectMany(path => ResourceData(methodInfo, path, withParameterNames));
      if (!result.Any()) {
        throw new ArgumentException("No data found for resource prefix: " + resourceNamePrefix);
      }
      return result;
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
