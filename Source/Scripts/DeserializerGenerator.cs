using System.Collections;
using System.CommandLine;
using System.Reflection;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using Type = System.Type;

namespace IntegrationTests;

public class DeserializerGenerator : PostParseAstVisitor {

  private HashSet<Type> typesWithHardcodedDeserializer = [typeof(Token), typeof(Specification<>)];

  private ClassDeclarationSyntax deserializeClass = (ClassDeclarationSyntax)SyntaxFactory.ParseMemberDeclaration(@"partial class Deserializer {}")!;
  private List<StatementSyntax> deserializeObjectCases = new();
  protected static Dictionary<Type, Dictionary<string, int>> parameterToSchemaPositions = new();

  public static Command GetCommand() {
    var result = new Command("generate-deserializer", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler((outputFile) => Handle(outputFile.FullName), fileArgument);
    return result;
  }

  public static async Task Handle(string outputFile) {
    var program = typeof(FileModuleDefinition);
    var generateParsedAst = new DeserializerGenerator();
    generateParsedAst.VisitTypesFromRoot(program);

    var deserializeUnit = SyntaxFactory.ParseCompilationUnit(@"
using System;
using System.Collections.Generic;
");
    var ns = SyntaxFactory.NamespaceDeclaration(SyntaxFactory.ParseName("Microsoft.Dafny"));
    var deserializeObjectSyntax = (MethodDeclarationSyntax)SyntaxFactory.ParseMemberDeclaration($@"
private object ReadObject(System.Type actualType) {{
  throw new Exception();
}}")!;
    generateParsedAst.deserializeObjectCases.Add(SyntaxFactory.ParseStatement("throw new Exception();"));
    deserializeObjectSyntax = deserializeObjectSyntax.WithBody(
      deserializeObjectSyntax.Body!.WithStatements(SyntaxFactory.List(generateParsedAst.deserializeObjectCases)));
    generateParsedAst.deserializeClass = generateParsedAst.deserializeClass.WithMembers(
      generateParsedAst.deserializeClass.Members.Add(deserializeObjectSyntax));
    ns = ns.AddMembers(generateParsedAst.deserializeClass);

    deserializeUnit = deserializeUnit.WithMembers(deserializeUnit.Members.Add(ns));
    await File.WriteAllTextAsync(outputFile, deserializeUnit.NormalizeWhitespace().ToFullString());
  }

  protected override void HandleClass(Type type) {
    var ownedFieldPosition = 0;
    var baseType = OverrideBaseType.GetOrDefault(type, () => type.BaseType);
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {

      ownedFieldPosition = parameterToSchemaPositions[baseType].Count;
    }
    var parameterToSchemaPosition = new Dictionary<string, int>();
    var schemaToConstructorPosition = new Dictionary<int, int>();
    parameterToSchemaPositions[type] = parameterToSchemaPosition;
    var statements = new StringBuilder();

    VisitParameters(type, (index, parameter, memberInfo) => {
      var parameterType = parameter.ParameterType;
      if (ExcludedTypes.Contains(parameterType)) {
        statements.AppendLine($"{parameterType} parameter{index} = null;");
        return;
      }

      if (memberInfo.GetCustomAttribute<BackEdge>() != null) {
        statements.AppendLine($"{parameterType} parameter{index} = null;");
        return;
      }

      if (memberInfo.DeclaringType != type) {
        if (parameterToSchemaPositions[memberInfo.DeclaringType!].TryGetValue(memberInfo.Name, out var schemaPosition)) {
          schemaToConstructorPosition[schemaPosition] = index;
          parameterToSchemaPosition[memberInfo.Name] = schemaPosition;
        }
        return;
      }

      var schemaPosition2 = ownedFieldPosition++;
      parameterToSchemaPosition[memberInfo.Name] = schemaPosition2;
      schemaToConstructorPosition[schemaPosition2] = index;
    });
    GenerateReadMethod(type, schemaToConstructorPosition, statements);
  }

  protected override void HandleEnum(Type type) {
    var deserializer = SyntaxFactory.ParseMemberDeclaration($@"
private {type.Name} Read{type.Name}() {{
  int ordinal = ReadInt32();
  return ({type.Name})ordinal;
}}")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(deserializer));
  }

  private void GenerateReadMethod(Type type, Dictionary<int, int> schemaToConstructorPosition,
    StringBuilder statements) {
    if (type.IsAbstract) {
      return;
    }

    var typeString = ToGenericTypeString(type);
    var constructor = GetParseConstructor(type);
    var parameters = constructor.GetParameters();

    var deserializeMethodName = $"Read{typeString}";
    if (typesWithHardcodedDeserializer.Contains(type.WithoutGenericArguments())) {
      return;
    }

    for (var schemaIndex = 0; schemaIndex < schemaToConstructorPosition.Count; schemaIndex++) {
      var constructorIndex = schemaToConstructorPosition[schemaIndex];
      var parameter = parameters[constructorIndex];

      var nullabilityContext = new NullabilityInfoContext();
      var nullabilityInfo = nullabilityContext.Create(parameter);
      bool isNullable = nullabilityInfo.ReadState == NullabilityState.Nullable;
      var parameterTypeReadCall = GetReadTypeCall(parameter.ParameterType, isNullable);
      statements.AppendLine(
        $"var parameter{constructorIndex} = {parameterTypeReadCall};");
    }

    AddReadMethodForType(parameters, statements, typeString, deserializeMethodName);
    AddReadOptionMethodForType(typeString, deserializeMethodName);
    deserializeObjectCases.Add(SyntaxFactory.ParseStatement($@"
if (actualType == typeof({typeString})) {{
  return {deserializeMethodName}();
}}
"));

  }

  private string GetReadTypeCall(Type parameterType, bool nullable) {
    string parameterTypeReadCall;
    var newType = MappedTypes.GetValueOrDefault(parameterType, parameterType);
    if (newType.IsArray) {
      var elementType = newType.GetGenericArguments()[0];
      var elementRead = GetReadTypeCall(elementType, false);
      var elementTypeString = ToGenericTypeString(elementType, false, false);
      return $"ReadArray<{elementTypeString}>(() => {elementRead})";
    }

    if (newType.IsGenericType && newType.IsAssignableTo(typeof(IEnumerable))) {
      var elementType = newType.GetGenericArguments()[0];
      var elementRead = GetReadTypeCall(elementType, false);
      var elementTypeString = ToGenericTypeString(elementType, false, false);
      return $"ReadList<{elementTypeString}>(() => {elementRead})";
    }

    var optionString = nullable ? "Option" : "";
    var genericTypeString = ToGenericTypeString(parameterType, true, false);
    if (newType.IsAbstract || newType == typeof(object)) {
      parameterTypeReadCall = $"ReadAbstract{optionString}<{genericTypeString}>()";
    } else {
      parameterTypeReadCall = $"Read{genericTypeString}{optionString}()";
    }

    return parameterTypeReadCall;
  }

  private void AddReadOptionMethodForType(string typeString, string deserializeMethodName) {
    var typedDeserialize = SyntaxFactory.ParseMemberDeclaration(@$"
 public {typeString} {deserializeMethodName}Option() {{
  if (ReadBool()) {{
     return default;
  }}
  return {deserializeMethodName}();
}}")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(typedDeserialize));
  }

  private void AddReadMethodForType(ParameterInfo[] parameters, StringBuilder statements, string typeString,
    string deserializeMethodName) {
    var parametersString = string.Join(", ", Enumerable.Range(0, parameters.Length).Select(index =>
      $"parameter{index}"));
    var typedDeserialize = SyntaxFactory.ParseMemberDeclaration(@$"
 public {typeString} {deserializeMethodName}() {{
  {statements}
  return new {typeString}({parametersString});
}}")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(typedDeserialize));
  }
}