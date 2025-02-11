using System.Reflection;
using Microsoft.Dafny;
using Microsoft.Extensions.FileSystemGlobbing.Internal.PatternContexts;
using Type = System.Type;

namespace IntegrationTests;

public abstract class PostParseAstVisitor {

  protected static Dictionary<Type, Type> overrideBaseType = new() {
    { typeof(TypeParameter), typeof(Declaration) },
    { typeof(ModuleDecl), typeof(Declaration) },
    { typeof(AttributedExpression), null }
  };

  protected static HashSet<Type> excludedTypes = [typeof(DafnyOptions)];

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

    var toVisit = new Stack<Type>();
    toVisit.Push(rootType);
    var visited = new HashSet<Type>();
    while (toVisit.Any()) {
      var current = toVisit.Pop();

      if (current.IsGenericType) {
        current = current.GetGenericTypeDefinition();
      }
      var baseType = overrideBaseType.GetOrDefault(current, () => current.BaseType);
      if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
        if (!visited.Contains(baseType)) {
          toVisit.Push(current);
          toVisit.Push(baseType);
          continue;
        }
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

      if (current.IsEnum) {
        HandleEnum(current);
      } else {
        VisitClass(current, toVisit, inheritors);
      }
    }
  }

  protected abstract void HandleEnum(Type current);

  protected void VisitParameters(Type type, Action<int, ParameterInfo, MemberInfo> handle) {
    var constructor = GetParseConstructor(type);
    var fields = type.GetFields().ToDictionary(f => f.Name.ToLower(), f => f);
    var properties = type.GetProperties().ToDictionary(p => p.Name.ToLower(), p => p);

    var parameters = constructor.GetParameters();
    for (var index = 0; index < parameters.Length; index++) {
      var parameter = constructor.GetParameters()[index];
      
      var memberInfo = fields.GetValueOrDefault(parameter.Name!.ToLower()) ??
                       (MemberInfo)properties.GetValueOrDefault(parameter.Name.ToLower())!;

      handle(index, parameter, memberInfo);
    }
  }
  
  private void VisitClass(Type type, Stack<Type> toVisit, IDictionary<Type, ISet<Type>> inheritors) {
    HandleClass(type);
    var baseType = overrideBaseType.GetOrDefault(type, () => type.BaseType);
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
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
          VisitType(child, toVisit);
        }
      }
    }

    VisitParameters(type, (_, parameter, field) => {
      if (excludedTypes.Contains(parameter.ParameterType)) {
        return;
      }
      if (field.GetCustomAttribute<BackEdge>() != null) {
        return;
      }

      var usedTyped = parameter.ParameterType;
      if (mappedTypes.TryGetValue(usedTyped, out var newType)) {
        usedTyped = newType;
      }

      VisitType(usedTyped, toVisit);
      foreach (var argument in usedTyped.GenericTypeArguments) {
        VisitType(argument, toVisit);
      }
    });
  }

  protected abstract void HandleClass(Type type);

  protected static void VisitType(Type type, Stack<Type> toVisit) {
    if (mappedTypes.TryGetValue(type, out var newType)) {
      type = newType;
    }
    toVisit.Push(type);
  }

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