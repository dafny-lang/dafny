using System;
using System.Collections.Generic;
using System.Reflection;

namespace Microsoft.Dafny;

class ReflectiveTraverser {

  public static void UpdateFieldsOfType<T>(object obj, Func<T, T> update) {
    foreach (var field in obj.GetType().GetRuntimeFields()) {
      if (field.FieldType == typeof(T)) {
        T value = (T)(field.GetValue(obj)!);
        var newValue = update(value);
        if (!Equals(newValue, value)) {
          field.SetValue(obj, newValue);
        }
      }

      if (field.FieldType.IsGenericType && 
          field.FieldType == typeof(List<T>)) {
        var list = (IList<T>)field.GetValue(obj)!;
        if (list == null) {
          continue;
        }
        for (var index = 0; index < list.Count; index++) {
          var element = list[index];
          var newValue = update(element);
          if (!Equals(newValue, element)) {
            list[index] = newValue;
          }
        }
      }
    }
  }
  public void UpdateStatements(Program program, Func<Statement, Statement> updateStatement) {
      
  }
}