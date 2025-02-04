using System.CommandLine;
using System.Numerics;
using System.Reflection;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;


public class GenerateParsedAst {
  private static HashSet<Type> excludedTypes = [typeof(DafnyOptions)];
  private static Dictionary<Type, Dictionary<string, int>> parameterToSchemaPositions = new();
  private static Dictionary<Type, Type> mappedTypes = new() {
    { typeof(Guid), typeof(string) },
    { typeof(IOrigin), typeof(SourceOrigin) },
    { typeof(Uri), typeof(string) }
  };

  private ClassDeclarationSyntax deserializeClass = (ClassDeclarationSyntax)ParseMemberDeclaration(@"partial class Deserializer {}")!;

  public static Command GetCommand() {
    var result = new Command("generate-parsed-ast", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    var fileArgument2 = new Argument<FileInfo>();
    result.AddArgument(fileArgument2);
    result.SetHandler((file1, file2) => Handle(file1.Name, file2.Name), fileArgument, fileArgument2);
    return result;
  }

  public static async Task Handle(string file, string file2) {
    var program = typeof(FileModuleDefinition);
    var generateParsedAst = new GenerateParsedAst();
    await File.WriteAllTextAsync(file, generateParsedAst.GenerateAll(program));
    var deserializeUnit = CompilationUnit();
    deserializeUnit = deserializeUnit.AddMembers(generateParsedAst.deserializeClass);
    await File.WriteAllTextAsync(file2, deserializeUnit.ToFullString());
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

    if (type.IsEnum) {
      var enumName = ToGenericTypeString(type);
      var enumm = EnumDeclaration(enumName);
      foreach (var name in Enum.GetNames(type)) {
        enumm = enumm.AddMembers(EnumMemberDeclaration(name));
      }

      return enumm;
    }

    if (type.IsGenericTypeParameter) {
      return null;
    }

    // Create a class
    var classDeclaration = ConvertTypeToSyntax(type);
    List<MemberDeclarationSyntax> newFields = new();

    var ownedFieldPosition = 0;
    var baseList = new List<BaseTypeSyntax>();
    if (type.BaseType != null && type.BaseType != typeof(ValueType) && type.BaseType != typeof(object)) {
      if (!visited.Contains(type.BaseType)) {
        toVisit.Push(type);
        toVisit.Push(type.BaseType);
        visited.Remove(type);
        return null;
      }
      baseList.Add(SimpleBaseType(ParseTypeName(ToGenericTypeString(type.BaseType))));
      ownedFieldPosition = parameterToSchemaPositions[type.BaseType].Count;

      var myParseConstructor = GetParseConstructor(type);
      var baseParseConstructor = GetParseConstructor(type.BaseType);
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
    for (var index = 0; index < parameters.Length; index++) {
      var parameter = constructor.GetParameters()[index];
      if (excludedTypes.Contains(parameter.ParameterType)) {
        // TODO fix.
        statements.AppendLine($"{parameter.ParameterType} parameter{index} = null;");
        continue;
      }

      if (parameter.GetCustomAttribute<BackEdge>() != null) {
        statements.AppendLine($"var parameter{index} = parent;");
        continue;
      }

      var memberInfo = fields.GetValueOrDefault(parameter.Name!.ToLower()) ??
                       (MemberInfo?)properties.GetValueOrDefault(parameter.Name.ToLower());

      if (memberInfo == null) {
        throw new Exception($"type {type}, parameter {parameter.Name}");
      }

      if (memberInfo.DeclaringType != type) {
        if (parameterToSchemaPositions[memberInfo.DeclaringType!].TryGetValue(memberInfo.Name, out var schemaPosition)) {
          schemaToConstructorPosition[schemaPosition] = index;
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

    for (var schemaIndex = 0; schemaIndex < schemaToConstructorPosition.Count; schemaIndex++) {
      var constructorIndex = schemaToConstructorPosition[schemaIndex];
      var parameter = parameters[constructorIndex];
      statements.AppendLine($"var parameter{constructorIndex} = Deserialize{parameter.ParameterType.Name}()");
    }

    var parametersString = string.Join(", ", Enumerable.Range(0, parameters.Length).Select(index => 
      $"parameter{index}"));
    var typedDeserialize = ParseMemberDeclaration(@$"
 private {type.Name} Deserialize{type.Name}() {{
  {statements}
  return new {type.Name}({parametersString})")!;
    deserializeClass = deserializeClass.WithMembers(deserializeClass.Members.Add(typedDeserialize)); 

    // Combine everything
    classDeclaration = classDeclaration.AddMembers(newFields.ToArray());
    return classDeclaration;
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

  public static string ToGenericTypeString(Type t) {
    if (mappedTypes.TryGetValue(t, out var newType)) {
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
        .Select(ToGenericTypeString).ToArray());
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