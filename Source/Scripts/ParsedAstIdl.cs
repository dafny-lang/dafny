using System.Collections;
using System.CommandLine;
using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;


public class GenerateParsedAst {
  private HashSet<Type> typesWithHardcodedDeserializer = [typeof(Token), typeof(Specification<>)];
  private static Dictionary<Type, Type> overrideBaseType = new() {
    { typeof(TypeParameter), typeof(Declaration) },
    { typeof(ModuleDecl), typeof(Declaration) },
    { typeof(AttributedExpression), null }
  };
  private static HashSet<Type> excludedTypes = [typeof(DafnyOptions)];
  private static Dictionary<Type, Dictionary<string, int>> parameterToSchemaPositions = new();
  private static Dictionary<Type, Type> mappedTypes = new() {
    { typeof(Guid), typeof(string) },
    { typeof(IOrigin), typeof(SourceOrigin) },
    { typeof(Uri), typeof(string) }
  };

  private ClassDeclarationSyntax deserializeClass = (ClassDeclarationSyntax)ParseMemberDeclaration(@"partial class Deserializer {}")!;
  private List<StatementSyntax> deserializeObjectCases = new();

  public static Command GetCommand() {
    var result = new Command("generate-parsed-ast", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    var fileArgument2 = new Argument<FileInfo>();
    result.AddArgument(fileArgument2);
    result.SetHandler((file1, file2) => Handle(file1.FullName, file2.FullName), fileArgument, fileArgument2);
    return result;
  }

  public static async Task Handle(string file, string file2) {
    var program = typeof(FileModuleDefinition);
    var generateParsedAst = new GenerateParsedAst();
    await File.WriteAllTextAsync(file, generateParsedAst.GenerateAll(program));
    var deserializeUnit = ParseCompilationUnit(@"
using System;
using System.Collections.Generic;
");
    var ns = NamespaceDeclaration(ParseName("Microsoft.Dafny"));
    var deserializeObjectSyntax = (MethodDeclarationSyntax)ParseMemberDeclaration($@"
private object DeserializeObject(System.Type actualType) {{
  throw new Exception();
}}")!;
    generateParsedAst.deserializeObjectCases.Add(ParseStatement("throw new Exception();"));
    deserializeObjectSyntax = deserializeObjectSyntax.WithBody(
      deserializeObjectSyntax.Body!.WithStatements(List(generateParsedAst.deserializeObjectCases)));
    generateParsedAst.deserializeClass = generateParsedAst.deserializeClass.WithMembers(
      generateParsedAst.deserializeClass.Members.Add(deserializeObjectSyntax));
    ns = ns.AddMembers(generateParsedAst.deserializeClass);

    deserializeUnit = deserializeUnit.WithMembers(deserializeUnit.Members.Add(ns));
    await File.WriteAllTextAsync(file2, deserializeUnit.NormalizeWhitespace().ToFullString());
  }

  public string GenerateAll(Type rootType) {
    var assembly = rootType.Assembly;
    var inheritors = assembly.GetTypes().Where(t => t.BaseType != null).GroupBy(t => t.BaseType!).ToDictionary(
      g => g.Key,
      g => (ISet<Type>)g.ToHashSet());

    var compilationUnit = CompilationUnit();

    var toVisit = new Stack<Type>();
    toVisit.Push(rootType);
    var visited = new HashSet<Type>();
    while (toVisit.Any()) {
      var current = toVisit.Pop();

      if (current.IsGenericType) {
        current = current.GetGenericTypeDefinition();
      }
      if (!visited.Add(current)) {
        continue;
      }

      if (current.Namespace != rootType.Namespace && current.Namespace != "Microsoft.Boogie") {
        continue;
      }
      var classDeclaration = GenerateClass(current, toVisit, visited, inheritors);
      if (classDeclaration != null) {
        compilationUnit = compilationUnit.AddMembers(classDeclaration);
      }
    }

    compilationUnit = compilationUnit.NormalizeWhitespace();


    var hasErrors = CheckCorrectness(compilationUnit);
    // if (hasErrors) {
    //   throw new Exception("Exception");
    // }
    return compilationUnit.ToFullString();
  }

  private BaseTypeDeclarationSyntax? GenerateClass(Type type,
    Stack<Type> toVisit,
    ISet<Type> visited,
    IDictionary<Type, ISet<Type>> inheritors) {
    var typeString = ToGenericTypeString(type);
    if (type.IsEnum) {
      return GenerateEnum(type, typeString);
    }

    if (type.IsGenericTypeParameter) {
      return null;
    }

    // Create a class
    var classDeclaration = ConvertTypeToSyntax(type);
    List<MemberDeclarationSyntax> newFields = new();

    var ownedFieldPosition = 0;
    var baseList = new List<BaseTypeSyntax>();
    var baseType = overrideBaseType.GetOrDefault(type, () => type.BaseType);
    
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
      if (!visited.Contains(baseType)) {
        toVisit.Push(type);
        toVisit.Push(baseType);
        visited.Remove(type);
        return null;
      }
      baseList.Add(SimpleBaseType(ParseTypeName(ToGenericTypeString(baseType))));
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

    if (baseList.Any()) { 
      classDeclaration = classDeclaration.WithBaseList(BaseList(SeparatedList(baseList)));
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
    if (constructor == null) {
      return null;
    }

    var fields = type.GetFields().ToDictionary(f => f.Name.ToLower(), f => f);
    var properties = type.GetProperties().ToDictionary(p => p.Name.ToLower(), p => p);

    var parameterToSchemaPosition = new Dictionary<string, int>();
    var schemaToConstructorPosition = new Dictionary<int, int>();
    var parameters = constructor.GetParameters();
    parameterToSchemaPositions[type] = parameterToSchemaPosition;
    var statements = new StringBuilder();
    ProcessParameters();
    // Combine everything
    classDeclaration = classDeclaration.AddMembers(newFields.ToArray());

    GenerateDeserializerMethod(type, constructor, schemaToConstructorPosition, parameters, statements, typeString);

    return classDeclaration;

    void ProcessParameters()
    {
      for (var index = 0; index < parameters.Length; index++) {
        var parameter = constructor.GetParameters()[index];
        if (excludedTypes.Contains(parameter.ParameterType)) {
          // TODO fix.
          statements.AppendLine($"{parameter.ParameterType} parameter{index} = null;");
          continue;
        }

        if (parameter.GetCustomAttribute<BackEdge>() != null) {
          statements.AppendLine($"{parameter.ParameterType} parameter{index} = null;");
          continue;
        }

        var memberInfo = fields.GetValueOrDefault(parameter.Name!.ToLower()) ??
                         (MemberInfo?)properties.GetValueOrDefault(parameter.Name.ToLower());
        memberInfo.GetCustomAttribute<BackEdge>();

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

      
        newFields.Add(FieldDeclaration(VariableDeclaration(
          ParseTypeName(ToGenericTypeString(usedTyped)),
          SeparatedList([VariableDeclarator(Identifier(parameter.Name!))]))));
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

  private BaseTypeDeclarationSyntax? GenerateEnum(Type type, string typeString)
  {
    var enumName = typeString;
    var enumm = EnumDeclaration(enumName);
    foreach (var name in Enum.GetNames(type)) {
      enumm = enumm.AddMembers(EnumMemberDeclaration(name));
    }

    var deserializer = ParseMemberDeclaration($@"
private {type.Name} Deserialize{type.Name}() {{
  int ordinal = DeserializeInt32();
  return ({type.Name})ordinal;
}}")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(deserializer));

    return enumm;
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

      var nullable = parameter.GetCustomAttribute<NullableAttribute>() != null;
      var parameterTypeReadCall = GetReadTypeCall(parameter.ParameterType, nullable);
      statements.AppendLine(
        $"var parameter{constructorIndex} = {parameterTypeReadCall};");
    }

    AddReadMethodForType(parameters, statements, typeString, deserializeMethodName);
    AddReadOptionMethodForType(typeString, deserializeMethodName);
    deserializeObjectCases.Add(ParseStatement($@"
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

    bool callObjectInstead = parameterType.IsAssignableTo(typeof(IEnumerable<object>));
    var checkOption = nullable;
            
    // Use once we use nullable annotation for the AST.
    var checkOption2 = parameterType.IsAssignableTo(typeof(object)) &&
                       parameterType.IsGenericType && parameterType.GetGenericTypeDefinition() == typeof(Nullable<>);
    var optionString = checkOption ? "Option" : "";
    
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
    var typedDeserialize = ParseMemberDeclaration(@$"
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
    var typedDeserialize = ParseMemberDeclaration(@$"
 public {typeString} {deserializeMethodName}() {{
  {statements}
  return new {typeString}({parametersString});
}}")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(typedDeserialize));
  }

  private static ConstructorInfo GetParseConstructor(Type type)
  {
    var constructors = type.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
    return constructors.Where(c => !c.IsPrivate &&
                                   !c.GetParameters().Any(p => p.ParameterType.IsAssignableTo(typeof(Cloner)))).MaxBy(c =>
      c.GetCustomAttribute<ParseConstructorAttribute>() == null ? c.GetParameters().Length : int.MaxValue)!;
  }

  public static ClassDeclarationSyntax ConvertTypeToSyntax(Type type) {
    // Get the base class name without generic parameters
    string className = type.IsGenericType ?
        type.Name.Substring(0, type.Name.IndexOf('`')) :
        type.Name;

    if (type.IsNested) {
      className = type.DeclaringType.Name + className;
    }

    // Create the class declaration with public modifier
    var classDecl = ClassDeclaration(className);

    // If the type is generic, add type parameters
    if (type.IsGenericType) {
      // Get generic type parameters
      var typeParameters = type.GetGenericArguments();

      // Create type parameter list
      var typeParamList = TypeParameterList(
          SeparatedList(
              typeParameters.Select(tp =>
                  TypeParameter(tp.Name))));

      // Add type parameter list to class declaration
      classDecl = classDecl.WithTypeParameterList(typeParamList);

      // Add constraints if any
      var constraintClauses = new List<TypeParameterConstraintClauseSyntax>();

      foreach (var typeParam in typeParameters) {
        var constraints = new List<TypeParameterConstraintSyntax>();

        // Get generic parameter constraints
        var paramConstraints = type.GetGenericArguments()
            .First(t => t.Name == typeParam.Name)
            .GetGenericParameterConstraints();

        // Add class/struct constraint if applicable
        var attributes = typeParam.GenericParameterAttributes;
        if ((attributes & GenericParameterAttributes.ReferenceTypeConstraint) != 0) {
          constraints.Add(ClassOrStructConstraint(SyntaxKind.ClassConstraint));
        }
        if ((attributes & GenericParameterAttributes.NotNullableValueTypeConstraint) != 0) {
          constraints.Add(ClassOrStructConstraint(SyntaxKind.StructConstraint));
        }

        // Add type constraints
        foreach (var constraint in paramConstraints) {
          if (constraint.IsInterface) {
            continue;
          }
          constraints.Add(
              TypeConstraint(ParseTypeName(constraint.Name)));
        }

        // Add constructor constraint if applicable
        if ((attributes & GenericParameterAttributes.DefaultConstructorConstraint) != 0) {
          constraints.Add(ConstructorConstraint());
        }

        // If we have any constraints, create the constraint clause
        if (constraints.Any()) {
          var constraintClause = TypeParameterConstraintClause(
              IdentifierName(typeParam.Name),
              SeparatedList(constraints));

          constraintClauses.Add(constraintClause);
        }
      }

      if (constraintClauses.Any()) {
        classDecl = classDecl.WithConstraintClauses(List(constraintClauses));
      }
    }

    return classDecl;
  }

  public static string ToGenericTypeString(Type t, bool useTypeMapping = true, bool mapNestedTypes = true) {
    if (useTypeMapping && mappedTypes.TryGetValue(t, out var newType)) {
      t = newType;
    }

    if (t.IsGenericTypeParameter) {
      return t.Name;
    }

    if (!t.IsGenericType) {
      var name = t.Name;
      if (t.IsNested) {
        name = t.DeclaringType.Name + name;
      }
      return name;
    }

    string genericTypeName = t.GetGenericTypeDefinition().Name;
    if (t.IsNested) {
      genericTypeName = t.DeclaringType.Name + genericTypeName;
    }
    genericTypeName = genericTypeName.Substring(0,
      genericTypeName.IndexOf('`'));
    string genericArgs = string.Join(",",
      t.GetGenericArguments()
        .Select(t => ToGenericTypeString(t, mapNestedTypes, mapNestedTypes)).ToArray());
    return genericTypeName + "<" + genericArgs + ">";
  }

  private static bool CheckCorrectness(CompilationUnitSyntax compilationUnit) {
    var namespaceDeclaration = NamespaceDeclaration(ParseName("Testing"));
    namespaceDeclaration = namespaceDeclaration.WithMembers(compilationUnit.Members);
    compilationUnit = CompilationUnit().AddMembers(namespaceDeclaration);
    compilationUnit = compilationUnit.AddUsings(
      UsingDirective(ParseName("System"))).AddUsings(
      UsingDirective(ParseName("System.Collections.Generic"))).AddUsings(
      UsingDirective(ParseName("System.Numerics")));

    // Create a list of basic references that most code will need
    var references = new List<string>
    {
      typeof(object).Assembly.Location,
      typeof(Console).Assembly.Location,
      typeof(System.Runtime.AssemblyTargetedPatchBandAttribute).Assembly.Location,
      typeof(List<>).Assembly.Location,
      typeof(BigInteger).Assembly.Location,
      typeof(ValueType).Assembly.Location
    }.Distinct().ToList();
    var syntaxTree = CSharpSyntaxTree.Create(compilationUnit);
    var compilation = CSharpCompilation.Create(
      assemblyName: "DynamicAssembly",
      syntaxTrees: new[] { syntaxTree },
      references: references.Select(p => MetadataReference.CreateFromFile(p)),
      options: new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
    var diagnostics = compilation.GetDiagnostics();
    var significantDiagnostics = diagnostics.Where(d =>
      d.Severity == DiagnosticSeverity.Error).ToList();
    var hasErrors = significantDiagnostics.Any();
    foreach (var diagnostic in significantDiagnostics) {
      Console.WriteLine(diagnostic.ToString());
    }
    return hasErrors;
  }
}

static class TypeExtensions {

  public static Type WithoutGenericArguments(this Type type) {
    return type.IsGenericType ? type.GetGenericTypeDefinition() : type;
  }
}