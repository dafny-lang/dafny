using System.CommandLine;
using System.Numerics;
using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;

public class ParsedAstGenerator : PostParseAstVisitor {
  private CompilationUnitSyntax compilationUnit = CompilationUnit();

  public static Command GetCommand() {
    var result = new Command("generate-parsed-ast", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler((file1) => Handle(file1.FullName), fileArgument);
    return result;
  }

  public static async Task Handle(string outputFile) {
    var generator = new ParsedAstGenerator();
    await File.WriteAllTextAsync(outputFile, generator.GenerateAll());
  }

  public string GenerateAll() {

    var rootType = typeof(FileModuleDefinition);
    VisitTypesFromRoot(rootType);
    compilationUnit = compilationUnit.NormalizeWhitespace();

    var hasErrors = CheckCorrectness(compilationUnit);
    // if (hasErrors) {
    //   throw new Exception("Exception");
    // }
    return compilationUnit.ToFullString();
  }

  protected override void HandleEnum(Type type) {
    var enumName = ToGenericTypeString(type);
    var enumm = EnumDeclaration(enumName);
    foreach (var name in Enum.GetNames(type)) {
      enumm = enumm.AddMembers(EnumMemberDeclaration(name));
    }
    compilationUnit = compilationUnit.AddMembers(enumm);
  }

  protected override void HandleClass(Type type) {
    var classDeclaration = GenerateClassHeader(type);
    List<MemberDeclarationSyntax> newFields = [];

    VisitParameters(type, (_, parameter, memberInfo) => {
      if (ExcludedTypes.Contains(parameter.ParameterType)) {
        return;
      }

      if (memberInfo.GetCustomAttribute<BackEdge>() != null) {
        return;
      }

      if (memberInfo.DeclaringType != type) {
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
    var baseType = OverrideBaseType.GetOrDefault(type, () => type.BaseType);
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
      baseList.Add(SimpleBaseType(ParseTypeName(ToGenericTypeString(baseType))));
    }

    if (baseList.Any()) {
      classDeclaration = classDeclaration.WithBaseList(BaseList(SeparatedList(baseList)));
    }

    classDeclaration = classDeclaration.AddMembers(newFields.ToArray());
    compilationUnit = compilationUnit.AddMembers(classDeclaration);
  }

  public static ClassDeclarationSyntax GenerateClassHeader(Type type) {
    string className = type.IsGenericType ?
        type.Name.Substring(0, type.Name.IndexOf('`')) :
        type.Name;

    if (type.IsNested) {
      className = type.DeclaringType!.Name + className;
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