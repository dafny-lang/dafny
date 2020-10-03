using System;
using System.Collections.Generic;

namespace XUnitExtensions {
  public class ForEachAttribute : Attribute {

    private readonly Type EnumeratorClass;
    
    public ForEachAttribute(Type enumeratorClass = null) {
      EnumeratorClass = enumeratorClass ?? typeof(IEnumerable<>);
    }

    public Type EnumerableTypeOf(Type elementType) {
      return EnumeratorClass.MakeGenericType(elementType);
    }
  }
}