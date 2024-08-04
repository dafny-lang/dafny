using System.Linq.Expressions;
using System.Reflection;

namespace CompilerBuilder.Generic;

public static class ExpressionTreeExtensions {
  public static Property<TContainer, TField> GetProperty<TContainer, TField>(this Expression<Func<TContainer, TField>> expr) {
    MemberExpression? memberExpression = null;
    
    var instanceExpr = Expression.Parameter(typeof(TContainer), "instance");
    
    if (expr.Body is MemberExpression { Member: FieldInfo field }) {
      memberExpression = Expression.Field(instanceExpr, field);
      if (field.IsInitOnly) {
        throw new ArgumentException($"Field {field.Name} is not writeable");
      }
    }
    
    if (expr.Body is MemberExpression { Member: PropertyInfo property }) {
      memberExpression = Expression.Property(instanceExpr, property);
      if (!property.CanRead) {
        throw new ArgumentException($"Property {property.Name} is not readable");
      }
      if (!property.CanWrite) {
        throw new ArgumentException($"Property {property.Name} is not writeable");
      }
    }

    if (memberExpression == null) {
      throw new ArgumentException();
    }
    
    var propertyObjExpr = Expression.Convert(memberExpression, typeof(TField));
    var getter = Expression.Lambda<Func<TContainer, TField>>(propertyObjExpr, instanceExpr).Compile();

    var parameter = Expression.Parameter(typeof(TField), "value");
    var setterBody = Expression.Assign(memberExpression, parameter);
    var setter = Expression.Lambda<Action<TContainer, TField>>(setterBody, instanceExpr, parameter).Compile();
    return new Property<TContainer, TField>(getter, setter);
  }
}