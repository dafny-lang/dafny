using System.CommandLine;
using System.Numerics;
using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Formatting;
using Microsoft.CodeAnalysis.Options;
using Microsoft.Dafny;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;


public class GenerateParsedAst {
  private static HashSet<Type> excludedTypes = [typeof(DafnyOptions)];
  private static Dictionary<Type,Type> mappedTypes = new() {
    { typeof(Guid), typeof(string) },
    { typeof(IOrigin), typeof(SourceOrigin) },
    { typeof(Uri), typeof(string) }
  };
  
  public static Command GetCommand() {
    var result = new Command("generate-parsed-ast", "");
    var fileArgument = new Argument<FileInfo>();
    result.AddArgument(fileArgument);
    result.SetHandler(file => Handle(file.Name), fileArgument);
    return result;
  }

  public static async Task Handle(string file) {
    var program = typeof(LiteralModuleDecl);
    await File.WriteAllTextAsync(file, GenerateAll(program));
  }
  
  public static string GenerateAll(Type rootType) {
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
        var classDeclaration = GenerateClass(current, toVisit, inheritors);
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

  private static BaseTypeDeclarationSyntax? GenerateClass(Type type, Stack<Type> toVisit, IDictionary<Type, ISet<Type>> inheritors)
  {
    // if (type.IsInterface) {
    //   string interfaceName = type.IsGenericType ? 
    //     type.Name.Substring(0, type.Name.IndexOf('`')) : 
    //     type.Name;
    //   return (InterfaceDeclarationSyntax)ParseMemberDeclaration($"interface {interfaceName} {{}}")!;
    // }
    
    if (type.IsEnum) {
      var enumName = ToGenericTypeString(type);
      var enumm = EnumDeclaration(enumName);
      foreach (var name in Enum.GetNames(type)) {
        enumm = enumm.AddMembers(EnumMemberDeclaration(name));
      }

      return enumm;
    }
    
    // Create a class
    var classDeclaration = ConvertTypeToSyntax(type);
    List<MemberDeclarationSyntax> newFields = new();

    var baseList = new List<BaseTypeSyntax>();
    if (type.BaseType != null && type.BaseType != typeof(ValueType) && type.BaseType != typeof(Object)) {
      toVisit.Push(type.BaseType);
      baseList.Add(SimpleBaseType(ParseTypeName(ToGenericTypeString(type.BaseType))));
    }

    // foreach(var @interface in type.GetInterfaces().Except(type.BaseType == null ? [] : type.BaseType.GetInterfaces())) {
    //   var genType = @interface.IsGenericType ? @interface.GetGenericTypeDefinition() : @interface;
    //   if (genType == typeof(IComparable<>) || genType == typeof(object)) {
    //     continue;
    //   }
    //   baseList.Add(SimpleBaseType(ParseTypeName(ToGenericTypeString(@interface))));
    // }

    if (baseList.Any()) {
      classDeclaration = classDeclaration.WithBaseList(BaseList(SeparatedList(baseList)));
    }

    if (inheritors.TryGetValue(type, out var children)) {
      foreach (var child in children) {
        toVisit.Push(child);
      }
    }

    var constructors = type.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
    var constructor = constructors.Where(c => !c.IsPrivate && 
      !c.GetParameters().Any(p => p.ParameterType.IsAssignableTo(typeof(Cloner)))).MaxBy(c => 
      c.GetCustomAttribute<ParseConstructorAttribute>() == null ? c.GetParameters().Length : int.MaxValue);
    if (constructor != null) {
      var fields = type.GetFields().ToDictionary(f => f.Name.ToLower(), f => f);
      var properties = type.GetProperties().ToDictionary(p => p.Name.ToLower(), p => p);
      
      foreach (var parameter in constructor.GetParameters()) {
        if (excludedTypes.Contains(parameter.ParameterType)) {
          continue;
        }

        if (parameter.GetCustomAttribute<BackEdge>() != null) {
          continue;
        }

        var memberInfo = fields.GetValueOrDefault(parameter.Name!.ToLower()) ??
                         (MemberInfo?)properties.GetValueOrDefault(parameter.Name.ToLower());

        if (memberInfo != null && memberInfo.DeclaringType != type) {
          continue;
        }
        
        var usedTyped = parameter.ParameterType;
        
        newFields.Add(FieldDeclaration(VariableDeclaration(
            
            ParseTypeName(ToGenericTypeString(usedTyped)),
          SeparatedList([VariableDeclarator(Identifier(parameter.Name!))]))));
        
        if (mappedTypes.TryGetValue(usedTyped, out var newType)) {
          usedTyped = newType;
        }
        toVisit.Push(usedTyped);
        foreach (var argument in usedTyped.GenericTypeArguments) {
          toVisit.Push(argument);
        }
      }
    }

    // Combine everything
    classDeclaration = classDeclaration.AddMembers(newFields.ToArray());
    return classDeclaration;
  }

  private static string GetTypeName(Type type)
  {
    var enumName = type.Name;
    if (type.IsNested) {
      enumName = type.DeclaringType.Name + enumName;
    }

    return enumName;
  }

  public static ClassDeclarationSyntax ConvertTypeToSyntax(Type type)
    {
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
        if (type.IsGenericType)
        {
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
            
            foreach (var typeParam in typeParameters)
            {
                var constraints = new List<TypeParameterConstraintSyntax>();

                // Get generic parameter constraints
                var paramConstraints = type.GetGenericArguments()
                    .First(t => t.Name == typeParam.Name)
                    .GetGenericParameterConstraints();

                // Add class/struct constraint if applicable
                var attributes = typeParam.GenericParameterAttributes;
                if ((attributes & GenericParameterAttributes.ReferenceTypeConstraint) != 0)
                {
                    constraints.Add(ClassOrStructConstraint(SyntaxKind.ClassConstraint));
                }
                if ((attributes & GenericParameterAttributes.NotNullableValueTypeConstraint) != 0)
                {
                    constraints.Add(ClassOrStructConstraint(SyntaxKind.StructConstraint));
                }

                // Add type constraints
                foreach (var constraint in paramConstraints)
                {
                    if (constraint.IsInterface) {
                      continue;
                    }
                    constraints.Add(
                        TypeConstraint(ParseTypeName(constraint.Name)));
                }

                // Add constructor constraint if applicable
                if ((attributes & GenericParameterAttributes.DefaultConstructorConstraint) != 0)
                {
                    constraints.Add(ConstructorConstraint());
                }
                
                // If we have any constraints, create the constraint clause
                if (constraints.Any())
                {
                    var constraintClause = TypeParameterConstraintClause(
                        IdentifierName(typeParam.Name),
                        SeparatedList(constraints));
                    
                    constraintClauses.Add(constraintClause);
                }
            }

            if (constraintClauses.Any())
            {
                classDecl = classDecl.WithConstraintClauses(List(constraintClauses));
            }
        }

        return classDecl;
    }
  
  public static string ToGenericTypeString(Type t)
  {
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