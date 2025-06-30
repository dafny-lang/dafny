using System.Collections.Frozen;
using System.CommandLine;
using System.Numerics;
using System.Reflection;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using Scripts;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;

public class SyntaxSchemaGenerator : SyntaxAstVisitor {
  private CompilationUnitSyntax compilationUnit = CompilationUnit();

  // Track the successfully generated types, so we can check that they include all those used by the Parser
  private ISet<Type> generatedTypes = new HashSet<Type>();

  public static Command GetCommand() {
    var result = new Command("generate-syntax-schema", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler((file1) => Handle(file1.FullName), fileArgument);
    return result;
  }

  public static async Task Handle(string outputFile) {
    var generator = new SyntaxSchemaGenerator();
    await File.WriteAllTextAsync(outputFile, generator.GenerateAll());
  }

  public string GenerateAll() {
    var rootType = typeof(FilesContainer);
    VisitTypesFromRoots([rootType, typeof(SourceOrigin), typeof(TokenRangeOrigin)]);
    compilationUnit = compilationUnit.NormalizeWhitespace(eol: "\n");

    var hasErrors = CheckCorrectness(compilationUnit);
    if (hasErrors) {
      throw new Exception("Exception");
    }
    CheckExpectedTypesGenerated();
    return compilationUnit.ToFullString();
  }

  /// <summary>
  /// Print all syntax class types that are constructed by the <see cref="Parser"/> but were not generated.
  /// Note that this excludes enum values that the parser assigns by identifier.
  /// </summary>
  private void CheckExpectedTypesGenerated() {
    var parserCode = ResourceLoader.GetResourceAsString("Parser.cs");

    // these patterns aren't complete, but they're good enough
    var newPattern = new Regex(@"new (?<type>\w[^(\n]*)\(");
    var commentPattern = new Regex(@"\/\*[^*]*\*\/");

    var ignoredTypes = new HashSet<string> { "", "string", "List", "Uri" };
    var expectedTypeNames = newPattern.Matches(parserCode)
      .SelectMany(match => {
        var typeSyntax = match.Groups["type"].Value;
        typeSyntax = commentPattern.Replace(typeSyntax, "");
        typeSyntax = typeSyntax.Replace(">", " ").Replace("<", " ").Replace(",", " ");
        return typeSyntax.Split(" ").Select(typeStr => typeStr.Trim());
      })
      .Except(ignoredTypes)
      .Select(typeStr => {
        const string prefix = "Microsoft.Dafny.";
        return typeStr.StartsWith(prefix) ? typeStr : prefix + typeStr;
      })
      .ToHashSet();

    var generatedTypeNames = generatedTypes
      .Select(type => CutOffGenericSuffixPartOfName(type.FullName!).Replace('+', '.'))
      .ToFrozenSet();
    // NOTE: these include types not "expected" from scanning Parser
    Console.WriteLine($"{generatedTypeNames.Count} types generated:");
    foreach (var name in generatedTypeNames.Order()) {
      Console.WriteLine($"\t{name}");
    }

    var ungeneratedTypeNames = expectedTypeNames.Except(generatedTypeNames).ToFrozenSet();
    if (ungeneratedTypeNames.Count != 0) {
      Console.WriteLine($"{ungeneratedTypeNames.Count} expected syntax types not generated:");
      foreach (var name in ungeneratedTypeNames.Order()) {
        Console.WriteLine($"\t{name}");
      }
    }
    Console.WriteLine($"{(expectedTypeNames.Count - ungeneratedTypeNames.Count)} of {expectedTypeNames.Count} expected syntax types generated");
  }

  protected override void HandleEnum(Type type) {
    var enumName = ToGenericTypeString(type);
    var enumm = EnumDeclaration(enumName);
    foreach (var name in Enum.GetNames(type)) {
      enumm = enumm.AddMembers(EnumMemberDeclaration(name));
    }
    compilationUnit = compilationUnit.AddMembers(enumm);
    generatedTypes.Add(type);
  }

  protected override void HandleClass(Type type) {
    var classDeclaration = GenerateClassHeader(type);
    List<MemberDeclarationSyntax> newFields = [];

    var baseType = GetBaseType(type);
    VisitParameters(type, (_, parameter) => {
      if (ExcludedTypes.Contains(parameter.ParameterType)) {
        return;
      }

      if (parameter.GetCustomAttribute<BackEdge>() != null) {
        return;
      }

      if (DoesMemberBelongToBase(type, parameter, baseType)) {
        return;
      }

      var nullabilityContext = new NullabilityInfoContext();
      var nullabilityInfo = nullabilityContext.Create(parameter);
      bool isNullable = nullabilityInfo.ReadState == NullabilityState.Nullable;
      var nullableSuffix = isNullable ? "?" : "";

      newFields.Add(FieldDeclaration(VariableDeclaration(
        ParseTypeName(ToGenericTypeString(parameter.ParameterType) + nullableSuffix),
        SeparatedList([VariableDeclarator(Identifier(parameter.Name!))]))));
    });

    var baseList = new List<BaseTypeSyntax>();
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
      baseList.Add(SimpleBaseType(ParseTypeName(ToGenericTypeString(baseType))));
    }

    if (baseList.Any()) {
      classDeclaration = classDeclaration.WithBaseList(BaseList(SeparatedList(baseList)));
    }

    classDeclaration = classDeclaration.AddMembers(newFields.ToArray());
    compilationUnit = compilationUnit.AddMembers(classDeclaration);
    generatedTypes.Add(type);
  }

  public static ClassDeclarationSyntax GenerateClassHeader(Type type) {
    string className = type.IsGenericType ?
        type.Name.Substring(0, type.Name.IndexOf('`')) :
        type.Name;

    if (type.IsNested) {
      className = type.DeclaringType!.Name + className;
    }

    var classDecl = ClassDeclaration(className);
    if (type.IsAbstract) {
      classDecl = classDecl.WithModifiers(TokenList(Token(SyntaxKind.AbstractKeyword)));
    }

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
      UsingDirective(ParseName("System")),
      UsingDirective(ParseName("System.Collections.Generic")),
      UsingDirective(ParseName("System.Numerics"))
    );

    // Create a list of basic references that most code will need
    var references = new List<string>
    {
      typeof(object).Assembly.Location,
      typeof(Console).Assembly.Location,
      typeof(System.Runtime.AssemblyTargetedPatchBandAttribute).Assembly.Location,
      typeof(List<>).Assembly.Location,
      typeof(BigInteger).Assembly.Location,
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