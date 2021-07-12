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

    private static Func<Source, IEnumerable<Target>> GetFunc(System.Type concreteType) {
      var castObj = Expr.Parameter(concreteType, "castObj");
      var objParam = Expr.Parameter(typeof(Source), "obj");
      var enumTargetType = typeof(IEnumerable<>).MakeGenericType(typeof(Target));
      var simpleMembers = new List<MemberExpression>();
      var enumMembers = new List<MemberExpression>();
      foreach (var member in concreteType.FindMembers(MemberTypes.Field, BindingFlags.Instance | BindingFlags.Public, null, null)) {
        var memberType = GetMemberType(member);
        var access = Expr.PropertyOrField(castObj, member.Name);
        if (memberType.IsAssignableTo(typeof(Target))) {
          simpleMembers.Add(access);
        }
        if (memberType.IsAssignableTo(enumTargetType)) {
          enumMembers.Add(access);
        }
      }
      var simpleMemberArray = Expr.NewArrayInit(typeof(Target), simpleMembers);
      var expr = enumMembers.Aggregate<Expr, Expr>(simpleMemberArray, (a, b) => Expr.Call(null, typeof(Enumerable).GetMethod("Concat", BindingFlags.Static)!, a, b));
      var block = Expr.Block(new[] { castObj }, Expr.Assign(castObj, Expr.TypeAs(objParam, concreteType)), expr);
      return Expr.Lambda<Func<Source, IEnumerable<Target>>>(block, objParam).Compile();
    }

    private static System.Type GetMemberType(MemberInfo member) {
      switch (member) {
        case FieldInfo fieldInfo:
          return fieldInfo.FieldType;
        case PropertyInfo propertyInfo:
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