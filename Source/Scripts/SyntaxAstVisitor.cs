using System.Collections.Frozen;
using System.Reflection;
using Microsoft.Dafny;
using Type = System.Type;

namespace Scripts;

/// <summary>
/// Visits the classes and fields of the Dafny AST that are used by the parser
/// </summary>
public abstract class SyntaxAstVisitor {

  /// <summary>
  /// Sometimes a type has an incorrect base-type in the sense that it does not
  /// use all the fields of the base-type. In those cases, we can override the bas type,
  /// so we do not need to refactor the Dafny AST
  /// </summary>
  protected static Dictionary<Type, Type?> OverrideBaseType = new() {
    { typeof(TypeParameter), typeof(Declaration) },
    { typeof(ModuleDecl), typeof(Declaration) },
    { typeof(SourceOrigin), typeof(IOrigin) },
    { typeof(TokenRangeOrigin), typeof(IOrigin) },
    { typeof(AttributedExpression), null }
  };

  /// <summary>
  /// Sometimes the parser sets fields that do not relate to the parsed source file
  /// </summary>
  protected static HashSet<Type> ExcludedTypes = [typeof(DafnyOptions)];

  /// <summary>
  /// When serializing, we may map some types to other types
  /// </summary>
  protected static Dictionary<Type, Type> MappedTypes = new() {
    { typeof(Guid), typeof(string) },
    { typeof(Uri), typeof(string) }
  };

  public void VisitTypesFromRoots(IReadOnlyList<Type> roots) {
    var assembly = roots.First().Assembly;
    var inheritors = assembly.GetTypes().Where(t => t.BaseType != null).GroupBy(t => t.BaseType!).ToDictionary(
      g => g.Key,
      g => (ISet<Type>)g.ToHashSet());

    var toVisit = new Stack<Type>();
    foreach (var root in roots) {
      toVisit.Push(root);
    }
    var visited = new HashSet<Type>();
    while (toVisit.Any()) {
      var current = toVisit.Pop();

      if (current.IsGenericType) {
        current = current.GetGenericTypeDefinition();
      }
      var baseType = OverrideBaseType.GetOrDefault(current, () => current.BaseType);
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

      if (current.Namespace != roots.First().Namespace && current.Namespace != "Microsoft.Boogie") {
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

  private void VisitClass(Type type, Stack<Type> toVisit, IDictionary<Type, ISet<Type>> inheritors) {
    HandleClass(type);
    var baseType = OverrideBaseType.GetOrDefault(type, () => type.BaseType);
    if (baseType != null && baseType != typeof(ValueType) && baseType != typeof(object)) {
      var myParseConstructor = GetParseConstructor(type)!;
      var baseParseConstructor = GetParseConstructor(baseType);
      var missingParameters = baseParseConstructor == null ? [] :
        baseParseConstructor.GetParameters().Select(p => p.Name)
          .Except(myParseConstructor.GetParameters().Select(p => p.Name))
          .ExceptBy(GetNonSerializedNames(type).Select(name => name.ToLower()), str => str?.ToLower())
          .ToList();
      if (missingParameters.Any()) {
        throw new Exception($"in type {type}, missing parameters: {string.Join(",", missingParameters)}");
      }
    }

    if (inheritors.TryGetValue(type, out var children)) {
      foreach (var child in children) {
        var goodConstructor = child.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance).
          FirstOrDefault(c => c.GetCustomAttribute<SyntaxConstructorAttribute>() != null);
        if (goodConstructor != null) {
          VisitType(child, toVisit);
        }
      }
    }

    VisitParameters(type, (_, parameter, field) => {
      if (ExcludedTypes.Contains(parameter.ParameterType)) {
        return;
      }
      if (field.GetCustomAttribute<BackEdge>() != null) {
        return;
      }

      if (field.DeclaringType != type) {
        return;
      }

      var usedTyped = parameter.ParameterType;
      VisitType(usedTyped, toVisit);
      foreach (var argument in usedTyped.GenericTypeArguments) {
        VisitType(argument, toVisit);
      }
    });
  }

  protected void VisitParameters(Type type, Action<int, ParameterInfo, MemberInfo> handle) {
    var constructor = GetParseConstructor(type);
    if (constructor == null) {
      return;
    }

    var fields = type.GetFields().ToDictionary(f => f.Name.ToLower(), f => f);
    var properties = type.GetProperties().
      DistinctBy(p => p.Name).
      ToDictionary(p => p.Name.ToLower(), p => p);

    var parameters = constructor.GetParameters();
    for (var index = 0; index < parameters.Length; index++) {
      var parameter = constructor.GetParameters()[index];

      var memberInfo = fields.GetValueOrDefault(parameter.Name!.ToLower()) ??
                       (MemberInfo)properties.GetValueOrDefault(parameter.Name.ToLower())!;

      if (memberInfo == null) {
        throw new Exception($"Could not find field or property corresponding to parameter {parameter.Name} in constructor of {type.Name}");
      }
      handle(index, parameter, memberInfo);
    }
  }

  protected abstract void HandleClass(Type type);

  protected static void VisitType(Type type, Stack<Type> toVisit) {
    if (MappedTypes.TryGetValue(type, out var newType)) {
      type = newType;
    }
    toVisit.Push(type);
  }

  protected static ConstructorInfo? GetParseConstructor(Type type) {
    var constructors = type.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance);
    return constructors.Where(c => !c.IsPrivate &&
                                   !c.GetParameters().Any(p => p.ParameterType.IsAssignableTo(typeof(Cloner)))).MaxBy(c =>
      c.GetCustomAttribute<SyntaxConstructorAttribute>() == null ? c.GetParameters().Length : int.MaxValue)!;
  }

  /// <summary>
  /// Return all field/property names appearing in <see cref="RedundantField"/>
  /// attributes of the specified type (or its base types).
  /// </summary>
  protected static IEnumerable<string> GetNonSerializedNames(Type type) {
    return type.GetCustomAttributes<RedundantField>()
      .Select(attr => attr.Name)
      .ToFrozenSet();
  }

  public static string ToGenericTypeString(Type t, bool useTypeMapping = true, bool mapNestedTypes = true,
    bool nestedDot = false) {
    if (useTypeMapping && MappedTypes.TryGetValue(t, out var newType)) {
      t = newType;
    }

    if (t.IsGenericTypeParameter) {
      return t.Name;
    }

    if (!t.IsGenericType) {
      var name = t.Name;
      if (t.IsNested) {
        name = t.DeclaringType!.Name + (nestedDot ? "." : "") + name;
      }
      return name;
    }

    string genericTypeName = t.GetGenericTypeDefinition().Name;
    if (t.IsNested) {
      genericTypeName = t.DeclaringType!.Name + genericTypeName;
    }
    genericTypeName = CutOffGenericSuffixPartOfName(genericTypeName);
    string genericArgs = string.Join(",",
      t.GetGenericArguments()
        .Select(argumentType => ToGenericTypeString(argumentType, mapNestedTypes, mapNestedTypes)).ToArray());
    return genericTypeName + "<" + genericArgs + ">";
  }

  public static string CutOffGenericSuffixPartOfName(string genericTypeName) {
    var tildeLocation = genericTypeName.IndexOf('`');
    return tildeLocation >= 0 ? genericTypeName.Substring(0, tildeLocation) : genericTypeName;
  }
}

static class TypeExtensions {

  public static Type WithoutGenericArguments(this Type type) {
    return type.IsGenericType ? type.GetGenericTypeDefinition() : type;
  }
}