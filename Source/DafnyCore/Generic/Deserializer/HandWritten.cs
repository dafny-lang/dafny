#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public partial class Deserializer(Uri uri, IDecoder decoder) {

  private Specification<T> ReadSpecification<T>() where T : Node {
    var parameter0 = DeserializeGeneric<SourceOrigin>();
    if (typeof(T) == typeof(FrameExpression)) {
      var parameter1 = ReadList<T>(() => (T)(object)ReadFrameExpression());
      var parameter2 = ReadAttributesOption();
      return new Specification<T>(parameter0, parameter1, parameter2);
    } else {
      var parameter1 = ReadList<T>(() => (T)(object)ReadAbstract<Expression>());
      var parameter2 = ReadAttributesOption();
      return new Specification<T>(parameter0, parameter1, parameter2);
    }
  }


  private List<T> ReadList<T>(Func<T> readElement) {
    return ReadArray<T>(readElement).ToList();
  }

  public Token ReadTokenOption() {
    return ReadToken();
  }

  public Token ReadToken() {
    var parameter0 = ReadInt32();
    var parameter1 = ReadInt32();
    return new Token(parameter0, parameter1) {
      Uri = uri
    };
  }

  private T[] ReadArray<T>(Func<T> readElement) {
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

  public T ReadAbstractOption<T>() {

    var isNull = decoder.ReadBool();
    if (isNull) {
      return default!;
    }

    return ReadAbstract<T>();
  }

  public T ReadAbstract<T>() {
    var typeName = decoder.ReadQualifiedName();
    var actualType = System.Type.GetType("Microsoft.Dafny." + typeName) ??
                 System.Type.GetType("System." + typeName) ?? throw new Exception($"Type not found: {typeName}");
    return DeserializeGeneric<T>(actualType);
  }

  public bool ReadBool() {
    return decoder.ReadBool();
  }

  public bool ReadBoolean() {
    return decoder.ReadBool();
  }

  public string? ReadStringOption() {
    var isNull = decoder.ReadBool();
    if (isNull) {
      return default;
    }
    return decoder.ReadString();
  }

  public string ReadString() {
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
      return (T)(object)ReadSourceOrigin();
    }

    return (T)ReadObject(actualType);
  }

  private int ReadInt32() {
    return decoder.ReadInt32();
  }
}