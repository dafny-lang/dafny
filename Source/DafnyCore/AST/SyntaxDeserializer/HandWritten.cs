#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.BaseTypes;

namespace Microsoft.Dafny;

/// <summary>
/// When using Dafny as a downstream tool, it can be useful to pass already parsed Dafny programs to Dafny,
/// since that allows filling the AST with source locations from other sources.
///
/// To enable this workflow for programs not written in C#,
/// Dafny supports consuming parsed programs from a serialized format.
/// 
/// This class allows reading Dafny programs that are encoded based on the schema defined in Source/Scripts/Syntax.cs.schema
///
/// The exact encoding can be varied using the instance of IDecoder, but it must adhere to these constraints:
/// - Instances of classes must contain the fields from the schema, in the order from the schema
/// - Arrays must specify their length first
/// - When encoding a field of an abstract class,
///   the concrete type of the field value must be specified before encoding its own fields.
/// 
/// </summary>
public partial class SyntaxDeserializer(IDecoder decoder) {
  private Uri? uri;

  private Specification<T> ReadSpecification<T>() where T : Node {
    if (typeof(T) == typeof(FrameExpression)) {
      var parameter1 = ReadListOption<T>(() => (T)(object)ReadFrameExpression());
      var parameter2 = ReadAttributesOption();
      return new Specification<T>(parameter1, parameter2);
    } else {
      var parameter1 = ReadList<T>(() => (T)(object)ReadAbstract<Expression>());
      var parameter2 = ReadAttributesOption();
      return new Specification<T>(parameter1, parameter2);
    }
  }

  private CasePattern<VT> ReadCasePattern<VT>() where VT : IVariable {
    if (typeof(VT) == typeof(BoundVar)) {
      var parameter0 = ReadAbstract<IOrigin>();
      var parameter1 = ReadString();
      var parameter2 = (VT)(object)ReadBoundVarOption();
      var parameter3 = ReadListOption(() => ReadCasePattern<VT>());
      return new CasePattern<VT>(parameter0, parameter1, parameter2, parameter3);
    } else if (typeof(VT) == typeof(LocalVariable)) {
      var parameter0 = ReadAbstract<IOrigin>();
      var parameter1 = ReadString();
      var parameter2 = (VT)(object)ReadLocalVariableOption();
      var parameter3 = ReadListOption(() => ReadCasePattern<VT>());
      return new CasePattern<VT>(parameter0, parameter1, parameter2, parameter3);
    } else {
      throw new Exception($"Unhandled CasePattern type: {typeof(VT)}");
    }
  }

  private CasePattern<VT>? ReadCasePatternOption<VT>() where VT : IVariable {
    return ReadIsNull() ? null : ReadCasePattern<VT>();
  }

  private List<T>? ReadListOption<T>(Func<T> readElement) {
    var isNull = decoder.ReadIsNull();
    if (isNull) {
      return null;
    }

    return ReadArray<T>(readElement).ToList();
  }

  private List<T> ReadList<T>(Func<T> readElement) {
    return ReadArray<T>(readElement).ToList();
  }

  public Token? ReadTokenOption() {
    var isNull = decoder.ReadIsNull();
    if (isNull) {
      return null;
    }
    return ReadToken();
  }

  public FilesContainer ReadFilesContainer() {
    var files = ReadList<FileStart>(() => ReadFileStart());
    return new FilesContainer(files);
  }

  public FileStart ReadFileStart() {
    var uri = ReadString();
    this.uri = new Uri(uri);
    var topLevelDecls = ReadList<TopLevelDecl>(() => ReadAbstract<TopLevelDecl>());
    return new FileStart(uri, topLevelDecls);
  }

  public Token ReadToken() {
    var parameter0 = ReadInt32();
    var parameter1 = ReadInt32();
    return new Token(parameter0, parameter1) {
      Uri = uri!
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

    var isNull = decoder.ReadIsNull();
    if (isNull) {
      return default!;
    }

    return ReadAbstract<T>();
  }

  public T ReadAbstract<T>() {
    var typeName = decoder.ReadQualifiedName();
    var actualType = System.Type.GetType("Microsoft.Dafny." + typeName) ??
                     System.Type.GetType("System." + typeName) ??
                     (typeName == "BigInteger" ? typeof(BigInteger) : null) ??
                     (typeName == "BigDec" ? typeof(BigDec) : null);
    if (actualType == null) {
      throw new Exception($"Type not found: {typeName}, expected type {typeof(T).Name}, position {decoder.Position}");
    }
    return DeserializeGeneric<T>(actualType);
  }

  public bool ReadIsNull() {
    return decoder.ReadIsNull();
  }

  public bool ReadBool() {
    return decoder.ReadBool();
  }

  public bool ReadBoolean() {
    return decoder.ReadBool();
  }

  public string? ReadStringOption() {
    var isNull = decoder.ReadIsNull();
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

    if (actualType == typeof(short)) {
      return (T)(object)decoder.ReadInt16();
    }

    if (actualType == typeof(int)) {
      return (T)(object)decoder.ReadInt32();
    }

    if (actualType == typeof(char)) {
      return (T)(object)decoder.ReadString();
    }

    if (actualType == typeof(long)) {
      return (T)(object)decoder.ReadInt64();
    }

    if (actualType == typeof(BigDec)) {
      return (T)(object)decoder.ReadBigDec();
    }

    if (actualType == typeof(BigInteger)) {
      return (T)(object)new BigInteger(decoder.ReadInt32());
    }

    if (actualType == typeof(SourceOrigin)) {
      return (T)(object)ReadSourceOrigin();
    }

    if (actualType == typeof(Token)) {
      return (T)(object)ReadToken();
    }

    return (T)ReadObject(actualType);
  }

  private int ReadInt32() {
    return decoder.ReadInt32();
  }
}

public class FilesContainer(List<FileStart> files) {
  public List<FileStart> Files { get; } = files;
}

public class FileStart {
  public string Uri { get; }
  public List<TopLevelDecl> TopLevelDecls { get; }

  public FileStart(string uri, List<TopLevelDecl> topLevelDecls) {
    Uri = uri;
    TopLevelDecls = topLevelDecls;
  }
}