using System;
using System.Collections.Generic;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Expr = System.Linq.Expressions.Expression;

namespace Microsoft.Dafny
{
  public class GetChildrenOfType<Target>
  {
    readonly IDictionary<System.Type, Func<dynamic, IEnumerable<Target>>> _getFunctions = 
      new Dictionary<System.Type, Func<dynamic, IEnumerable<Target>>>();
    
    readonly IDictionary<System.Type, Delegate> _overrides = 
      new Dictionary<System.Type, Delegate>();
    
    readonly IDictionary<System.Type, ParameterExpression> _params = 
      new Dictionary<System.Type, ParameterExpression>();
    
    readonly IDictionary<System.Type, Expr> _expressions = 
      new Dictionary<System.Type, Expr>();

    private readonly Func<MemberInfo, System.Type, bool> _memberPredicate;
    private readonly ISet<System.Type> _ignoreTheseAbstractTypesExceptionOtherwise;

    public GetChildrenOfType(Func<MemberInfo, System.Type, bool> memberPredicate = null, ISet<System.Type> ignoreTheseAbstractTypesExceptionOtherwise = null) {
      _memberPredicate = memberPredicate;
      _ignoreTheseAbstractTypesExceptionOtherwise = ignoreTheseAbstractTypesExceptionOtherwise;
    }
    
    public void Override<Source>(Func<Source, IEnumerable<Target>> func) {
      _overrides[typeof(Source)] = func;
    }

    private Func<object, IEnumerable<Target>> GetFunc(System.Type concreteType) {
      var castObj = GetParam(concreteType);
      var inter = GetTargetsExprCached(concreteType);
      if (inter == null) {
        return obj => Enumerable.Empty<Target>();
      }

      var objParam = Expr.Parameter(typeof(object), "outerObj");
      var block = Expr.Block(new[] {castObj}, Expr.Assign(castObj, Expr.TypeAs(objParam, concreteType)), inter);
      var result = Expr.Lambda<Func<object, IEnumerable<Target>>>(block, objParam).Compile();
      return result;
    }

    private static readonly MethodInfo ConcatMethod = 
      typeof(Enumerable).GetMethod("Concat", BindingFlags.Static | BindingFlags.Public)!.MakeGenericMethod(typeof(Target));

    public static IEnumerable<TResult> NotOverloadedSelectMany<TSource, TResult>(IEnumerable<TSource> source, Func<TSource, IEnumerable<TResult>> selector) {
      return source.SelectMany(selector);
    }

    private static readonly MethodInfo SelectManyMethod = typeof(GetChildrenOfType<Target>).GetMethod("NotOverloadedSelectMany");

    private Expr /*?*/ GetTargetsExprCached(System.Type type) {
      if (!_expressions.TryGetValue(type, out var result)) {
        _expressions[type] = null;
        result = GetTargetsExpr(type);
        _expressions[type] = result;
      }

      return result;
    }

    ParameterExpression GetParam(System.Type type) {
      if (!_params.TryGetValue(type, out var result)) {
        result = Expr.Parameter(type);
        _params[type] = result;
      }

      return result;
    }
    
    // Does not support traversal of recursive data structures like LList
    // TODO better support properties
    private Expr/*?*/ GetTargetsExpr(System.Type type) {
      var value = GetParam(type);
      if (_overrides.ContainsKey(type)) {
        var methodInfo = _overrides[type].Method;
        var target = _overrides[type].Target;
        return Expr.Call(target == null ? null : Expr.Constant(target), methodInfo, value);
      }

      // Can we make this check so it throws for all types with subtypes?
      if (type.IsAbstract) {
        if (_ignoreTheseAbstractTypesExceptionOtherwise != null && !_ignoreTheseAbstractTypesExceptionOtherwise.Contains(type)) {
          throw new Exception($"Cannot derive behavior for abstract type {type}.");
        }

        return null;
      }
      
      if (type.IsPrimitive || type.IsEnum || !type.Assembly.FullName.Contains("Dafny")) {
        return null;
      }
      
      var enumTargetType = typeof(IEnumerable<>).MakeGenericType(typeof(Target));
      var enumObjectType = typeof(IEnumerable<>).MakeGenericType(typeof(object));
      var simpleMembers = new List<MemberExpression>();
      var enumerableMembers = new List<Expr>();
      foreach (var member in type.FindMembers(MemberTypes.Field | MemberTypes.Property, BindingFlags.Instance | BindingFlags.Public, null, null)) {
        var memberType = GetMemberType(member);
        if (memberType == null)
          continue;
        
        if (_memberPredicate != null && !_memberPredicate(member, memberType)) {
          continue;
        }

        if (member is PropertyInfo propertyInfo) {
          if (GetBackingField(propertyInfo) == null) {
            continue;
          }
        }
        
        var access = Expr.PropertyOrField(value, member.Name);
        if (memberType.IsAssignableTo(typeof(Target))) {
          simpleMembers.Add(access);
        } else if (memberType.IsAssignableTo(enumTargetType)) {
          // NullSafe is required here because ForallStmt.ForallExpressions can be null. Maybe we should change that.
          enumerableMembers.Add(MakeNullSafe(access, Expr.TypeAs(access, enumTargetType)));
        } else if (memberType.IsAssignableTo(enumObjectType)) {
        
          var elementType = memberType.GenericTypeArguments[0];
          
          // Used for BlockStmt.Body
          if (_memberPredicate != null && !_memberPredicate(member, elementType)) {
            continue;
          }
          
          var fieldExpr = GetTargetsExprCached(elementType);
          if (fieldExpr != null) {;
            Expr selector = Expr.Lambda(fieldExpr, false, GetParam(elementType));
            var appliedSelectMany = SelectManyMethod.MakeGenericMethod(elementType, typeof(Target));
            var call = Expr.Call(null, appliedSelectMany, access, selector);
            
            // NullSafe is required here because Specification.Expression can be null. Maybe we should change that.
            enumerableMembers.Add(MakeNullSafe(access, call));
          }
        } else {
          var fieldVar = GetParam(memberType);
          var fieldExpr = GetTargetsExprCached(memberType);
          if (fieldExpr != null) {
            enumerableMembers.Add(Expr.Block(new []{ fieldVar}, Expr.Assign(fieldVar, access), MakeNullSafe(fieldVar, fieldExpr)));
          }
        }
      }

      var simpleMemberArray = Expr.NewArrayInit(typeof(Target), simpleMembers);
      var expr = enumerableMembers.Aggregate<Expr, Expr>(simpleMemberArray, (a, b) => Expr.Call(null, ConcatMethod, a, b));
      var nonEmpty = simpleMembers.Any() || enumerableMembers.Any();
      var inter = nonEmpty ? expr : null;
      return inter;
    }

    Expr MakeNullSafe(Expr inner, Expr outer) {
      return Expr.Condition(Expr.ReferenceEqual(inner, Expr.Constant(null)),
        Expr.Constant(Enumerable.Empty<Target>(), typeof(IEnumerable<Target>)), outer);
      
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
      // Maybe move the nullCheck to the fields.
      return func(source).Where(x => x != null);
    } 
    
    /*
     Doesn't always work, for example for the following code:
    private Expression term;
    public Expression Term { get { return term; } }

    public void UpdateTerm(Expression newTerm) {
      term = newTerm;
    }
     */
    public static FieldInfo GetBackingField(PropertyInfo propertyInfo) {
      if (propertyInfo == null)
        throw new ArgumentNullException(nameof(propertyInfo));
      if (!propertyInfo.CanRead || !propertyInfo.GetGetMethod(nonPublic: true).IsDefined(typeof(CompilerGeneratedAttribute), inherit: true))
        return null;
      var backingFieldName = GetBackingFieldName(propertyInfo.Name);
      var backingField = propertyInfo.DeclaringType?.GetField(backingFieldName, BindingFlags.Instance | BindingFlags.NonPublic);
      if (backingField == null)
        return null;
      if (!backingField.IsDefined(typeof(CompilerGeneratedAttribute), inherit: true))
        return null;
      return backingField;
    }
    
    const String Prefix = "<";
    const String Suffix = ">k__BackingField";
    private static String GetBackingFieldName(String propertyName) => $"{Prefix}{propertyName}{Suffix}";
  }
}