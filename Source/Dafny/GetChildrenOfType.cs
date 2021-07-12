using System;
using System.Collections.Generic;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;

using Expr = System.Linq.Expressions.Expression;

namespace Microsoft.Dafny
{
  // Consider supporting null. Consider supporting indirection "this.Attributes.SubExpressions(Attributes)"
  class GetChildrenOfType<Source, Target>
  {
    readonly IDictionary<System.Type, Func<Source, IEnumerable<Target>>> _getFunctions = 
      new Dictionary<System.Type, Func<Source, IEnumerable<Target>>>();

    private int varCounter = 0;

    private Func<Source, IEnumerable<Target>> GetFunc(System.Type concreteType) {
      var castObj = Expr.Parameter(concreteType, "castObj");
      var inter = GetTargetsExpr(new HashSet<System.Type>(), concreteType, castObj);
      if (inter == null) {
        return obj => Enumerable.Empty<Target>();
      }

      var objParam = Expr.Parameter(typeof(Source), "obj");
      var block = Expr.Block(new[] {castObj}, Expr.Assign(castObj, Expr.TypeAs(objParam, concreteType)), inter);
      return Expr.Lambda<Func<Source, IEnumerable<Target>>>(block, objParam).Compile();
    }

    static MethodInfo concatMethod = typeof(Enumerable).GetMethod("Concat", BindingFlags.Static | BindingFlags.Public)!.MakeGenericMethod(typeof(Target));
    
    private Expr? GetTargetsExpr(ISet<System.Type> visited, System.Type type, ParameterExpression value) {
      if (type.IsPrimitive || type.IsEnum || !type.Assembly.FullName.Contains("Dafny")) {
        return null;
      }
      
      if (!visited.Add(type))
        return null;
      
      var enumTargetType = typeof(IEnumerable<>).MakeGenericType(typeof(Target));
      var simpleMembers = new List<MemberExpression>();
      var enumerableMembers = new List<Expr>();
      foreach (var member in type.FindMembers(MemberTypes.Field | MemberTypes.Property, BindingFlags.Instance | BindingFlags.Public, null, null)) {
        var memberType = GetMemberType(member);
        if (memberType == null)
          continue;
        
        var access = Expr.PropertyOrField(value, member.Name);
        if (memberType.IsAssignableTo(typeof(Target))) {
          simpleMembers.Add(access);
        } else if (memberType.IsAssignableTo(enumTargetType)) {
          enumerableMembers.Add(access);
        } else {
          var fieldVar = Expr.Parameter(memberType, $"var{varCounter}");
          var fieldExpr = GetTargetsExpr(visited, memberType, fieldVar);
          if (fieldExpr != null) {
            varCounter++;
            enumerableMembers.Add(Expr.Block(new []{ fieldVar}, Expr.Assign(fieldVar, access), fieldExpr));
          }
        }
      }

      var simpleMemberArray = Expr.NewArrayInit(typeof(Target), simpleMembers);
      var expr = enumerableMembers.Aggregate<Expr, Expr>(simpleMemberArray, (a, b) => Expr.Call(null, concatMethod, a, b));
      var nonEmpty = simpleMembers.Any() || enumerableMembers.Any();
      var inter = nonEmpty ? expr : null;
      return inter;
    }

    private static System.Type? GetMemberType(MemberInfo member) {
      switch (member) {
        case FieldInfo fieldInfo:
          return fieldInfo.FieldType;
        case PropertyInfo propertyInfo:
          if (propertyInfo.GetIndexParameters().Any())
            return null;
          
          return propertyInfo.PropertyType;
        default:
          throw new InvalidOperationException();
      }
    }

    public IEnumerable<Target> GetTargets(Source source) {
      var key = source.GetType();
      if (_getFunctions.TryGetValue(key, out var existingFunc )) {
        return existingFunc(source).Where(x => x != null);
      }

      var func = GetFunc(key);
      _getFunctions[key] = func;
      return func(source).Where(x => x != null);
    } 
  }
}