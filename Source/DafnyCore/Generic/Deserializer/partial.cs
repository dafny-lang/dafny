#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Text;
using Microsoft.Extensions.DependencyInjection;

namespace Microsoft.Dafny;

public partial class Deserializer(Uri uri, IDecoder decoder) {

  private Specification<T> DeserializeSpecification<T>() where T : Node {
    var parameter0 = DeserializeGeneric<SourceOrigin>();
    if (typeof(T) == typeof(FrameExpression)) {
      var parameter1 = DeserializeList<T>(() => (T)(object)DeserializeFrameExpression());
      var parameter2 = DeserializeAttributesOption();
      return new Specification<T>(parameter0, parameter1, parameter2);
    } else {
      var parameter1 = DeserializeList<T>(() => (T)(object)DeserializeAbstract<Expression>());
      var parameter2 = DeserializeAttributesOption();
      return new Specification<T>(parameter0, parameter1, parameter2);
    }
  }

  
  private List<T> DeserializeList<T>(Func<T> readElement) {
    return DeserializeArray<T>(readElement).ToList();
  }

  public Token DeserializeTokenOption() {
    return DeserializeToken();
  }
  
  public Token DeserializeToken()
  {
    var parameter0 = DeserializeInt32();
    var parameter1 = DeserializeInt32();
    return new Token(parameter0, parameter1) {
      Uri = uri
    };
  }

  private T[] DeserializeArray<T>(Func<T> readElement) {
    var length = decoder.ReadInt32();
    var array = new T[length];
    for (int i = 0; i < length; i++) {
      array.SetValue(readElement(), i);
    }
    return array;
  }

  private T Value<T>() {
    return DeserializeGeneric<T>();
  }

  public T DeserializeAbstractOption<T>() {

    if (Nullable.GetUnderlyingType(typeof(T)) != null) {
      var isNull = decoder.ReadBool();
      if (isNull) {
        return default;
      }
    }
    
    return DeserializeAbstract<T>();
  }
  
  public T DeserializeAbstract<T>() {
    var actualType = typeof(T);
    var typeName = decoder.ReadQualifiedName();
    actualType = System.Type.GetType("Microsoft.Dafny." + typeName) ??
                 System.Type.GetType("System." + typeName) ?? throw new Exception($"Type not found: {typeName}");
    return DeserializeGeneric<T>(actualType);
  }

  public bool ReadBool() {
    return decoder.ReadBool();
  }

  public bool DeserializeBoolean() {
    return decoder.ReadBool();
  }
  
  public bool DeserializeBool() {
    return decoder.ReadBool();
  }
  
  public string DeserializeString() {
    return decoder.ReadString();
  }

  public T DeserializeGeneric<T>() {
    return DeserializeGeneric<T>(typeof(T));
  }

  public T DeserializeGeneric<T>(System.Type actualType) {

    if (actualType == typeof(string)) {
      return (T)(object)decoder.ReadString();
    }
    
    if (actualType == typeof(bool)) {
      return (T)(object)decoder.ReadBool();
    }

    if (actualType == typeof(int)) {
      return (T)(object)decoder.ReadInt32();
    }

    if (actualType == typeof(IOrigin) || actualType == typeof(SourceOrigin)) {
      return (T)(object)DeserializeSourceOrigin();
    }

    // if (Nullable.GetUnderlyingType(actualType) != null) {
    //   var isNull = decoder.ReadBool();
    //   if (isNull) {
    //     return default;
    //   }
    // }
    
    return (T)DeserializeObject(actualType);
  }

  private int DeserializeInt32() {
    return decoder.ReadInt32();
  }
}