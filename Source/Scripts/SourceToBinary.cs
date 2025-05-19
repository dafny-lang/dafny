using System.Collections;
using System.CommandLine;
using System.Numerics;
using System.Reflection;
using System.Text;
using Microsoft.BaseTypes;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using ISymbol = Microsoft.CodeAnalysis.ISymbol;
using Type = System.Type;

namespace Scripts;

public class SourceToBinary {

  public static Command GetCommand() {
    var result = new Command("source-to-binary", "");
    var inputArgument = new Argument<FileInfo>("input", "Dafny source file");
    result.AddArgument(inputArgument);
    var outputArgument = new Argument<FileInfo>("output", "File to write binary output to");
    result.AddArgument(outputArgument);
    result.SetHandler((file1, file2) => Handle(file1.FullName,
      new StreamWriter(file2.FullName)),
      inputArgument, outputArgument);
    return result;
  }

  public static async Task Handle(string inputFile, TextWriter outputFile) {
    var options = DafnyOptions.Default;
    var errorReporter = new BatchErrorReporter(options);
    var input = await File.ReadAllTextAsync(inputFile);
    var parseResult = await ProgramParser.Parse(input, new Uri(Path.GetFullPath(inputFile)), errorReporter);
    if (errorReporter.HasErrors) {
      var errors = errorReporter.AllMessagesByLevel[ErrorLevel.Error];
      var exceptions = errors.Select(diagnostic =>
        new Exception($"Parsing error: {errorReporter.FormatDiagnostic(diagnostic)}"));
      throw new AggregateException($"{errors.Count} errors occurred during parsing", exceptions);
    }

    var syntaxSchema = ResourceLoader.GetResourceAsString("Syntax.cs-schema");
    var output = new StringBuilder();
    var textEncoder = new TextEncoder(output);
    SyntaxTree syntaxTree = CSharpSyntaxTree.ParseText(syntaxSchema);
    var references = new MetadataReference[]
    {
      MetadataReference.CreateFromFile(typeof(object).Assembly.Location),
      MetadataReference.CreateFromFile(typeof(List<>).Assembly.Location),
      MetadataReference.CreateFromFile(typeof(Enumerable).Assembly.Location)
    };
    var compilation = CSharpCompilation.Create(
      "TypeAnalysis",
      new[] { syntaxTree },
      references,
      new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
    var semanticModel = compilation.GetSemanticModel(syntaxTree);

    var root = syntaxTree.GetCompilationUnitRoot();

    var typeDeclarations = root.DescendantNodes().OfType<TypeDeclarationSyntax>();
    var types = typeDeclarations.Select(t => semanticModel.GetDeclaredSymbol(t)!).ToList();

    var filesContainer = new FilesContainer(parseResult.Program.Files.Select(f =>
      new FileStart(f.Origin.Uri.LocalPath, f.TopLevelDecls.ToList())).ToList());
    new Serializer(textEncoder, types).Serialize(filesContainer);
    await outputFile.WriteAsync(output);
    await outputFile.FlushAsync();
  }
}



public class Serializer(IEncoder encoder, IReadOnlyList<INamedTypeSymbol> parsedAstTypes) {
  private readonly Dictionary<string, List<string>> fieldsPerType =
    parsedAstTypes.ToDictionary(t => t.Name, t =>
      GetAllMembers(t).OfType<IFieldSymbol>().Select(f => f.Name.ToLower()).ToList());

  private static IEnumerable<ISymbol> GetAllMembers(INamedTypeSymbol type) {
    var baseType = type.BaseType;
    if (baseType == null || baseType.SpecialType == SpecialType.System_Object) {
      return type.GetMembers();
    }

    return GetAllMembers(baseType).Concat(type.GetMembers());
  }

  private static readonly Dictionary<string, string> SimpleTypeNameMapping = new()
  {
    { "Int32", "Int32" }
  };

  public void Serialize(object obj) {
    SerializeObject(obj);
  }

  public void SerializeValue(object? value, Type expectedType, bool isNullable) {
    if (isNullable) {
      encoder.WriteNullable(value == null);
      if (value == null) {
        return;
      }
    }

    if (value == null) {
      throw new InvalidOperationException("Unexpected null value for non-nullable type");
    }

    if (expectedType.IsGenericType && expectedType.GetGenericTypeDefinition() == typeof(Nullable<>)) {
      expectedType = Nullable.GetUnderlyingType(expectedType)!;
    }

    if (expectedType.IsEnum) {
      encoder.WriteInt((int)value);
      return;
    }

    if (expectedType.IsArray) {
      SerializeArray((Array)value, expectedType.GetElementType()!);
      return;
    }

    if (value is IList list) {
      SerializeList(list, expectedType.GetGenericArguments()[0]);
      return;
    }

    bool isAbstract = expectedType == typeof(object) ||
                      expectedType is { IsClass: true, IsAbstract: true } || expectedType.IsInterface;

    if (isAbstract) {
      if (value is OriginWrapper originWrapper) {
        value = originWrapper.WrappedOrigin;
      }
      var actualType = value.GetType();

      string simpleName = actualType.Name;
      if (SimpleTypeNameMapping.TryGetValue(simpleName, out var mappedName)) {
        simpleName = mappedName;
      }
      encoder.WriteQualifiedName(simpleName);
    }

    switch (value) {
      case string s:
        encoder.WriteString(s);
        break;
      case IDictionary dict:
        SerializeMap(dict, expectedType);
        break;
      case BigInteger i:
        encoder.WriteInt(i);
        break;
      case BigDec i:
        encoder.WriteBigDec(i);
        break;
      case int i:
        encoder.WriteInt(i);
        break;
      case bool b:
        encoder.WriteBool(b);
        break;
      default:
        SerializeObject(value);
        break;
    }
  }

  private void SerializeList(IList list, Type elementType) {
    int length = list.Count;
    encoder.WriteInt(length);

    for (int i = 0; i < length; i++) {
      // In C#, we'll need to determine nullability differently
      bool isNullable = elementType.IsClass ||
                        (elementType.IsGenericType &&
                         elementType.GetGenericTypeDefinition() == typeof(Nullable<>));
      SerializeValue(list[i], elementType, isNullable);
    }
  }

  private void SerializeArray(Array array, Type elementType) {
    int length = array.Length;
    encoder.WriteInt(length);

    for (int i = 0; i < length; i++) {
      bool isNullable = elementType.IsClass ||
                        (elementType.IsGenericType &&
                         elementType.GetGenericTypeDefinition() == typeof(Nullable<>));
      SerializeValue(array.GetValue(i), elementType, isNullable);
    }
  }

  private void SerializeMap(IDictionary map, Type mapType) {
    encoder.WriteInt(map.Count);

    Type[] genericArgs = mapType.GetGenericArguments();
    Type keyType = genericArgs[0];
    Type valueType = genericArgs[1];

    foreach (DictionaryEntry entry in map) {
      bool keyNullable = keyType.IsClass ||
                         (keyType.IsGenericType &&
                          keyType.GetGenericTypeDefinition() == typeof(Nullable<>));
      bool valueNullable = valueType.IsClass ||
                           (valueType.IsGenericType &&
                            valueType.GetGenericTypeDefinition() == typeof(Nullable<>));

      SerializeValue(entry.Key, keyType, keyNullable);
      SerializeValue(entry.Value, valueType, valueNullable);
    }
  }

  private void SerializeObject(object obj) {
    var instanceType = obj.GetType();
    Type? foundType = instanceType;
    while (foundType != null && !fieldsPerType.ContainsKey(
             SyntaxAstVisitor.CutOffGenericSuffixPartOfName(foundType.Name))) {
      foundType = foundType.BaseType;
    }

    if (foundType == null) {
      throw new Exception($"Could not find schema type for {instanceType}");
    }

    var fieldNames = fieldsPerType[SyntaxAstVisitor.CutOffGenericSuffixPartOfName(foundType.Name)];
    var fieldsPerName = new Dictionary<string, FieldInfo>();
    foreach (var fieldInfo in GetSerializableFields(foundType)) {
      var fieldName = fieldInfo.Name;
      if (fieldName.StartsWith("<") && fieldName.EndsWith("k__BackingField")) {
        // Support auto properties
        fieldName = fieldName.Substring(1, fieldName.IndexOf(">", StringComparison.Ordinal) - 1);
      } else if (fieldName.StartsWith("<") && fieldName.EndsWith(">P")) {
        // Support fields from a primary constructor
        fieldName = fieldName.Substring(1, fieldName.Length - 3);
      }

      // If this is an overridden field, overwrite the entry
      fieldsPerName[fieldName.ToLower()] = fieldInfo;
    }

    foreach (var fieldName in fieldNames) {
      var field = fieldsPerName.GetValueOrDefault(fieldName);
      if (field == null) {
        continue;
      }

      try {
        object? value = field.GetValue(obj);

        var nullabilityContext = new NullabilityInfoContext();
        var nullabilityInfo = nullabilityContext.Create(field);
        bool isNullable = nullabilityInfo.ReadState == NullabilityState.Nullable;
        SerializeValue(value, field.FieldType, isNullable);
      } catch (Exception e) {
        throw new InvalidOperationException($"Failed to serialize field: {field.Name}", e);
      }
    }
  }

  private static IEnumerable<FieldInfo> GetSerializableFields(Type type) {
    var fields = new List<FieldInfo>();
    Type? result = type;
    while (result != null && result != typeof(object)) {
      fields.InsertRange(0, result.GetFields(BindingFlags.DeclaredOnly |
                                             BindingFlags.Instance |
                                             BindingFlags.Public |
                                             BindingFlags.NonPublic));
      result = result.BaseType;
    }
    return fields;
  }
}