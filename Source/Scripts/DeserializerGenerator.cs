using System.Collections;
using System.CommandLine;
using System.Numerics;
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
private object DeserializeObject(System.Type actualType) {{
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

  protected override void HandleType(Type current, Stack<Type> toVisit, HashSet<Type> visited, Dictionary<Type, ISet<Type>> inheritors) {
    if (current.IsEnum) {
      HandleEnum(current);
    } else {
      HandleClass(current, toVisit, visited, inheritors);
    }
  }

  private void HandleClass(Type type,
    Stack<Type> toVisit,
    ISet<Type> visited,
    IDictionary<Type, ISet<Type>> inheritors) {
    var typeString = ToGenericTypeString(type);

    var ownedFieldPosition = 0;
    var baseType = overrideBaseType.GetOrDefault(type, () => type.BaseType);
    
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
      if (!visited.Contains(baseType)) {
        toVisit.Push(type);
        toVisit.Push(baseType);
        visited.Remove(type);
        return;
      }
      ownedFieldPosition = parameterToSchemaPositions[baseType].Count;

      var myParseConstructor = GetParseConstructor(type);
      var baseParseConstructor = GetParseConstructor(baseType);
      var missingParameters =
        baseParseConstructor.GetParameters().Select(p => p.Name)
          .Except(myParseConstructor.GetParameters().Select(p => p.Name));
      if (missingParameters.Any()) {
        throw new Exception("");
      }
    }


    if (inheritors.TryGetValue(type, out var children)) {
      foreach (var child in children) {
        var goodConstructor = child.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance).
          FirstOrDefault(c => c.GetCustomAttribute<ParseConstructorAttribute>() != null);
        if (goodConstructor != null) {
          toVisit.Push(child);
        }
      }
    }

    var constructor = GetParseConstructor(type);

    var fields = type.GetFields().ToDictionary(f => f.Name.ToLower(), f => f);
    var properties = type.GetProperties().ToDictionary(p => p.Name.ToLower(), p => p);

    var parameterToSchemaPosition = new Dictionary<string, int>();
    var schemaToConstructorPosition = new Dictionary<int, int>();
    var parameters = constructor.GetParameters();
    parameterToSchemaPositions[type] = parameterToSchemaPosition;
    var statements = new StringBuilder();
    ProcessParameters();

    GenerateDeserializerMethod(type, constructor, schemaToConstructorPosition, parameters, statements, typeString);

    void ProcessParameters()
    {
      for (var index = 0; index < parameters.Length; index++) {
        var parameter = constructor.GetParameters()[index];
        if (excludedTypes.Contains(parameter.ParameterType)) {
          statements.AppendLine($"{parameter.ParameterType} parameter{index} = null;");
          continue;
        }

        if (parameter.GetCustomAttribute<BackEdge>() != null) {
          statements.AppendLine($"{parameter.ParameterType} parameter{index} = null;");
          continue;
        }

        var memberInfo = fields.GetValueOrDefault(parameter.Name!.ToLower()) ??
                         (MemberInfo?)properties.GetValueOrDefault(parameter.Name.ToLower());

        if (memberInfo == null) {
          throw new Exception($"type {type}, parameter {parameter.Name}");
        }
        if (memberInfo.GetCustomAttribute<BackEdge>() != null) {
          statements.AppendLine($"{parameter.ParameterType} parameter{index} = null;");
          continue;
        }

        if (memberInfo.DeclaringType != type) {
          if (parameterToSchemaPositions[memberInfo.DeclaringType!].TryGetValue(memberInfo.Name, out var schemaPosition)) {
            schemaToConstructorPosition[schemaPosition] = index;
            parameterToSchemaPosition[memberInfo.Name] = schemaPosition;
          }
          continue;
        }

        var usedTyped = parameter.ParameterType;
      
        var schemaPosition2 = ownedFieldPosition++;
        parameterToSchemaPosition[memberInfo.Name] = schemaPosition2;
        schemaToConstructorPosition[schemaPosition2] = index;

        if (mappedTypes.TryGetValue(usedTyped, out var newType)) {
          usedTyped = newType;
        }

        toVisit.Push(usedTyped);
        foreach (var argument in usedTyped.GenericTypeArguments) {
          toVisit.Push(argument);
        }
      }
    }
  }

  private void HandleEnum(Type type)
  {
    var deserializer = SyntaxFactory.ParseMemberDeclaration($@"
private {type.Name} Deserialize{type.Name}() {{
  int ordinal = DeserializeInt32();
  return ({type.Name})ordinal;
}}")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(deserializer));
  }

  private void GenerateDeserializerMethod(Type type, ConstructorInfo constructor, Dictionary<int, int> schemaToConstructorPosition,
    ParameterInfo[] parameters, StringBuilder statements, string typeString) {
    if (type.IsAbstract || !constructor.IsPublic) {
      return;
    }

    var deserializeMethodName = $"Deserialize{typeString}";
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

  private string GetReadTypeCall(Type parameterType, bool nullable)
  {
    string parameterTypeReadCall;
    var newType = mappedTypes.GetValueOrDefault(parameterType, parameterType);
    if (newType.IsArray) {
      var elementType = newType.GetGenericArguments()[0];
      var elementRead = GetReadTypeCall(elementType, false);
      var elementTypeString = ToGenericTypeString(elementType, false, false);
      return $"DeserializeArray<{elementTypeString}>(() => {elementRead})";
    }
    
    if (newType.IsGenericType && newType.IsAssignableTo(typeof(IEnumerable))) {
      var elementType = newType.GetGenericArguments()[0];
      var elementRead = GetReadTypeCall(elementType, false);
      var elementTypeString = ToGenericTypeString(elementType, false, false);
      return $"DeserializeList<{elementTypeString}>(() => {elementRead})";
    }

    var optionString = nullable ? "Option" : "";
    var genericTypeString = ToGenericTypeString(parameterType, true, false);
    if (newType.IsAbstract || newType == typeof(object)) {
      parameterTypeReadCall = $"DeserializeAbstract{optionString}<{genericTypeString}>()";
    } else {
      parameterTypeReadCall = $"Deserialize{genericTypeString}{optionString}()";
    }

    return parameterTypeReadCall;
  }

  private void AddReadOptionMethodForType(string typeString, string deserializeMethodName)
  {
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
    string deserializeMethodName)
  {
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