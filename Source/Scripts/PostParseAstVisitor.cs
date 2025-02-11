using System.Collections;
using System.CommandLine;
using System.Numerics;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;
using Type = System.Type;

namespace IntegrationTests;


public abstract class PostParseAstVisitor {

  protected static Dictionary<Type, Type> overrideBaseType = new() {
    { typeof(TypeParameter), typeof(Declaration) },
    { typeof(ModuleDecl), typeof(Declaration) },
    { typeof(AttributedExpression), null }
  };

  protected static HashSet<Type> excludedTypes = [typeof(DafnyOptions)];
  protected static Dictionary<Type, Dictionary<string, int>> parameterToSchemaPositions = new();

  protected static Dictionary<Type, Type> mappedTypes = new() {
    { typeof(Guid), typeof(string) },
    { typeof(IOrigin), typeof(SourceOrigin) },
    { typeof(Uri), typeof(string) }
  };


  public void VisitTypesFromRoot(Type rootType) {
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

      if (current.IsGenericTypeParameter) {
        continue;
      }
      
      HandleType(current, toVisit, visited, inheritors);
    }
  }

  protected abstract void HandleType(Type current, Stack<Type> toVisit, HashSet<Type> visited,
    Dictionary<Type, ISet<Type>> inheritors);

  protected static ConstructorInfo GetParseConstructor(Type type)
  {
    var constructors = type.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
    return constructors.Where(c => !c.IsPrivate &&
                                   !c.GetParameters().Any(p => p.ParameterType.IsAssignableTo(typeof(Cloner)))).MaxBy(c =>
      c.GetCustomAttribute<ParseConstructorAttribute>() == null ? c.GetParameters().Length : int.MaxValue)!;
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

}

static class TypeExtensions {

  public static Type WithoutGenericArguments(this Type type) {
    return type.IsGenericType ? type.GetGenericTypeDefinition() : type;
  }
}