using System;
using System.Collections.Generic;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;
using Expr = System.Linq.Expressions.Expression;

namespace Microsoft.Dafny
{
  public class FilledInByResolution : Attribute
  {
    
  }
  
  // Consider supporting null. Consider supporting indirection "this.Attributes.SubExpressions(Attributes)"
  public class GetChildrenOfType<Target>
  {
    readonly IDictionary<System.Type, Func<dynamic, IEnumerable<Target>>> _getFunctions = 
      new Dictionary<System.Type, Func<dynamic, IEnumerable<Target>>>();
    
    readonly IDictionary<System.Type, Delegate> _overrides = 
      new Dictionary<System.Type, Delegate>();

    private readonly Func<MemberInfo, bool> _memberPredicate;

    public GetChildrenOfType(Func<MemberInfo, bool> memberPredicate = null) {
      _memberPredicate = memberPredicate;
    }

    public void Override<Source>(Func<Source, IEnumerable<Target>> func) {
      _overrides[typeof(Source)] = func;
    }

    private Func<object, IEnumerable<Target>> GetFunc(System.Type concreteType) {
      var castObj = Expr.Parameter(concreteType, "castObj");
      var inter = GetTargetsExpr(new HashSet<System.Type>(), concreteType, castObj);
      if (inter == null) {
        return obj => Enumerable.Empty<Target>();
      }

      var objParam = Expr.Parameter(typeof(object), "obj");
      var block = Expr.Block(new[] {castObj}, Expr.Assign(castObj, Expr.TypeAs(objParam, concreteType)), inter);
      return Expr.Lambda<Func<object, IEnumerable<Target>>>(block, objParam).Compile();
    }

    private static readonly MethodInfo ConcatMethod = 
      typeof(Enumerable).GetMethod("Concat", BindingFlags.Static | BindingFlags.Public)!.MakeGenericMethod(typeof(Target));
    
    private Expr/*?*/ GetTargetsExpr(ISet<System.Type> visited, System.Type type, ParameterExpression value) {
      if (_overrides.ContainsKey(type)) {
        var methodInfo = _overrides[type].Method;
        var target = _overrides[type].Target;
        return Expr.Call(target == null ? null : Expr.Constant(target), methodInfo, value);
      }
      
      if (type.IsPrimitive || type.IsEnum || !type.Assembly.FullName.Contains("Dafny")) {
        return null;
      }
      
      if (!visited.Add(type))
        return null;
      
      var enumTargetType = typeof(IEnumerable<>).MakeGenericType(typeof(Target));
      var simpleMembers = new List<MemberExpression>();
      var enumerableMembers = new List<Expr>();
      foreach (var member in type.FindMembers(MemberTypes.Field /*| MemberTypes.Property*/, BindingFlags.Instance | BindingFlags.Public, null, null)) {
        if (_memberPredicate != null && !_memberPredicate(member)) {
          continue;
        }
        var memberType = GetMemberType(member);
        if (memberType == null)
          continue;
        
        var access = Expr.PropertyOrField(value, member.Name);
        if (memberType.IsAssignableTo(typeof(Target))) {
          simpleMembers.Add(access);
        } else if (memberType.IsAssignableTo(enumTargetType)) {
          enumerableMembers.Add(access);
        } else {
          // TODO support IEnumerable<> of nested target carriers.
          var fieldVar = Expr.Parameter(memberType, $"obj");
          var fieldExpr = GetTargetsExpr(visited, memberType, fieldVar);
          if (fieldExpr != null) {
            enumerableMembers.Add(Expr.Block(new []{ fieldVar}, Expr.Assign(fieldVar, access), fieldExpr));
          }
        }
      }

      var simpleMemberArray = Expr.NewArrayInit(typeof(Target), simpleMembers);
      var expr = enumerableMembers.Aggregate<Expr, Expr>(simpleMemberArray, (a, b) => Expr.Call(null, ConcatMethod, a, b));
      var nonEmpty = simpleMembers.Any() || enumerableMembers.Any();
      var inter = nonEmpty ? expr : null;
      return inter;
    }

    private static System.Type/*?*/ GetMemberType(MemberInfo member) {
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

    public IEnumerable<Target> GetTargets(object source) {
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