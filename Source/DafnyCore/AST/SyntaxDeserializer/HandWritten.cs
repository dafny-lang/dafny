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

  public readonly List<Action<SystemModuleManager>> SystemModuleModifiers = [];


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
    var files = ReadList<FileHeader>(ReadFileStart);
    return new FilesContainer(files);
  }

  public FileHeader ReadFileStart() {
    var uri = ReadString();
    var isLibrary = ReadBool();
    this.uri = DafnyFile.CreateCrossPlatformUri(uri);
    var topLevelDecls = ReadList(ReadAbstract<TopLevelDecl>);
    return new FileHeader(uri, isLibrary, topLevelDecls);
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

    if (actualType == typeof(MultiSelectExpr)) {
      return (T)(object)ReadMultiSelectExpr();
    }

    if (actualType == typeof(AllocateArray)) {
      return (T)(object)ReadAllocateArray();
    }

    if (actualType == typeof(Function)) {
      return (T)(object)ReadFunction();
    }

    return (T)ReadObject(actualType);
  }

  private int ReadInt32() {
    return decoder.ReadInt32();
  }

  // For MultiSelectExpr and AllocateArray, we need specific cases to properly update the
  // SystemModuleModifiers, as done in Dafny.atg
  public MultiSelectExpr ReadMultiSelectExpr() {
    var parameter0 = ReadAbstract<IOrigin>();
    var parameter1 = ReadAbstract<Expression>();
    var parameter2 = ReadList<Expression>(() => ReadAbstract<Expression>());
    SystemModuleModifiers.Add(b => b.ArrayType(parameter2.Count, new IntType(), true));
    return new MultiSelectExpr(parameter0, parameter1, parameter2);
  }
  public AllocateArray ReadAllocateArray() {
    var parameter0 = ReadAbstract<IOrigin>();
    var parameter4 = ReadAttributesOption();
    var parameter1 = ReadAbstractOption<Type>();
    var parameter2 = ReadList<Expression>(() => ReadAbstract<Expression>());
    var parameter3 = ReadAbstractOption<Expression>();
    SystemModuleModifiers.Add(b => b.ArrayType(parameter2.Count, new IntType(), true));
    return new AllocateArray(parameter0, parameter1, parameter2, parameter3, parameter4);
  }

  public Function ReadFunction() {
    var parameter0 = ReadAbstract<IOrigin>();
    var parameter1 = ReadName();
    var parameter16 = ReadAttributesOption();
    var parameter3 = ReadBoolean();
    var parameter17 = ReadAbstractOption<IOrigin>();
    var parameter5 = ReadList<TypeParameter>(() => ReadTypeParameter());
    var parameter6 = ReadList<Formal>(() => ReadFormal());
    var parameter9 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
    var parameter11 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
    var parameter10 = ReadSpecification<FrameExpression>();
    var parameter12 = ReadSpecification<Expression>();
    var parameter2 = ReadBoolean();
    var parameter4 = ReadBoolean();
    var parameter7 = ReadFormalOption();
    var parameter8 = ReadAbstract<Type>();
    var parameter13 = ReadAbstractOption<Expression>();
    var parameter14 = ReadAbstractOption<IOrigin>();
    var parameter15 = ReadBlockStmtOption();
    SystemModuleModifiers.Add(b => b.CreateArrowTypeDecl(parameter6.Count));
    return new Function(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15, parameter16, parameter17);
  }
}

public class FilesContainer(List<FileHeader> files) {
  public List<FileHeader> Files { get; } = files;
}

public class FileHeader(string uri, bool isLibrary, List<TopLevelDecl> topLevelDecls) {
  public string Uri { get; } = uri;
  public bool IsLibrary { get; } = isLibrary;

  public List<TopLevelDecl> TopLevelDecls { get; } = topLevelDecls;
}