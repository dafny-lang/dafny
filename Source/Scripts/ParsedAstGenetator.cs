using System.Collections;
using System.CommandLine;
using System.Numerics;
using System.Reflection;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;


public class ParsedAstGenerator : PostParseAstVisitor {
  private CompilationUnitSyntax compilationUnit;

  public static Command GetCommand() {
    var result = new Command("generate-parsed-ast", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler((file1) => Handle(file1.FullName), fileArgument);
    return result;
  }

  public static async Task Handle(string outputFile) {
    var program = typeof(FileModuleDefinition);
    var generateParsedAst = new DeserializerGenerator();
    await File.WriteAllTextAsync(outputFile, generateParsedAst.GenerateAll(program));
  }

  public string GenerateAll(Type rootType) {

    compilationUnit = CompilationUnit();
    VisitTypesFromRoot(rootType);
    compilationUnit = compilationUnit.NormalizeWhitespace();
    
    var hasErrors = CheckCorrectness(compilationUnit);
    if (hasErrors) {
      throw new Exception("Exception");
    }
    return compilationUnit.ToFullString();
  }

  protected override void HandleType(Type current, Stack<Type> toVisit, HashSet<Type> visited,
    Dictionary<Type, ISet<Type>> inheritors) {
    
    var classDeclaration = GenerateType(current, toVisit, visited, inheritors);
    if (classDeclaration != null) {
      compilationUnit = compilationUnit.AddMembers(classDeclaration);
    }
  }

  private BaseTypeDeclarationSyntax? GenerateType(Type type,
    Stack<Type> toVisit,
    ISet<Type> visited,
    IDictionary<Type, ISet<Type>> inheritors) {
    var typeString = ToGenericTypeString(type);
    if (type.IsEnum) {
      return GenerateEnum(type, typeString);
    }

    return GenerateClass(type, toVisit, visited, inheritors);
  }

  private static BaseTypeDeclarationSyntax? GenerateClass(Type type, Stack<Type> toVisit, ISet<Type> visited, IDictionary<Type, ISet<Type>> inheritors)
  {
    var classDeclaration = GenerateClassHeader(type);
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
    classDeclaration = classDeclaration.AddMembers(newFields.ToArray());

    return classDeclaration;

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
        var nullabilityContext = new NullabilityInfoContext();
        var nullabilityInfo = nullabilityContext.Create(parameter);
        bool isNullable = nullabilityInfo.ReadState == NullabilityState.Nullable;
        var nullableSuffix = isNullable ? "?" : "";
      
        newFields.Add(FieldDeclaration(VariableDeclaration(
          ParseTypeName(ToGenericTypeString(usedTyped) + nullableSuffix),
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

  private BaseTypeDeclarationSyntax GenerateEnum(Type type, string typeString)
  {
    var enumName = typeString;
    var enumm = EnumDeclaration(enumName);
    foreach (var name in Enum.GetNames(type)) {
      enumm = enumm.AddMembers(EnumMemberDeclaration(name));
    }
    return enumm;
  }

  public static ClassDeclarationSyntax GenerateClassHeader(Type type) {
    string className = type.IsGenericType ?
        type.Name.Substring(0, type.Name.IndexOf('`')) :
        type.Name;

    if (type.IsNested) {
      className = type.DeclaringType.Name + className;
    }

    var classDecl = ClassDeclaration(className);

    if (type.IsGenericType) {
      var typeParameters = type.GetGenericArguments();

      var typeParamList = TypeParameterList(
          SeparatedList(
              typeParameters.Select(tp =>
                  TypeParameter(tp.Name))));

      classDecl = classDecl.WithTypeParameterList(typeParamList);

      var constraintClauses = new List<TypeParameterConstraintClauseSyntax>();

      foreach (var typeParam in typeParameters) {
        var constraints = new List<TypeParameterConstraintSyntax>();

        var paramConstraints = type.GetGenericArguments()
            .First(t => t.Name == typeParam.Name)
            .GetGenericParameterConstraints();

        var attributes = typeParam.GenericParameterAttributes;
        if ((attributes & GenericParameterAttributes.ReferenceTypeConstraint) != 0) {
          constraints.Add(ClassOrStructConstraint(SyntaxKind.ClassConstraint));
        }
        if ((attributes & GenericParameterAttributes.NotNullableValueTypeConstraint) != 0) {
          constraints.Add(ClassOrStructConstraint(SyntaxKind.StructConstraint));
        }

        foreach (var constraint in paramConstraints) {
          if (constraint.IsInterface) {
            continue;
          }
          constraints.Add(
              TypeConstraint(ParseTypeName(constraint.Name)));
        }

        if ((attributes & GenericParameterAttributes.DefaultConstructorConstraint) != 0) {
          constraints.Add(ConstructorConstraint());
        }

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