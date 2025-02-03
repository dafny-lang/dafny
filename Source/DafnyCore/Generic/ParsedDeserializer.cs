using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Text;
using Microsoft.Dafny;
using Type = System.Type;

namespace IntegrationTests;

public partial class ParsedDeserializer(string input) {
  private int position;

  public T Deserialize<T>() {
    position = 0;
    var result = (T)DeserializeValue(typeof(T));
    if (position != input.Length) {
      throw new Exception();
    }
    return result;
  }

  private object DeserializeValue(Type expectedType) {
    SkipWhitespace();

    if (TryMatch("null")) {
      return null;
    }

    // Check for type override
    Type actualType = expectedType;

    if (TryMatch("\"")) {
      return ReadString();
    }

    if (actualType.IsEnum) {
      int ordinal = ReadNumber();
      return Enum.ToObject(actualType, ordinal);
    }

    if (actualType.IsArray) {
      return ReadArray(actualType.GetElementType());
    }

    if (actualType.IsAssignableTo(typeof(IList))) {
      var elementType = actualType.GetGenericArguments()[0];
      var value = ReadArray(elementType);
      var constructionType = typeof(List<>).MakeGenericType(elementType);
      return constructionType.
        GetConstructor(BindingFlags.Public | BindingFlags.Instance, [value.GetType()])!.Invoke([value]);
    }
    
    if (TryMatch("+")) {
      string typeName = ReadUntil(':');
      actualType = Type.GetType("Microsoft.Dafny." + typeName) ??
                   Type.GetType("System." + typeName) ?? throw new Exception($"Type not found: {typeName}");
      position++; // skip ':'
    }

    if (IsSimpleType(actualType)) {
      return ConvertSimpleType(ReadToken(), actualType);
    }
    
    // if (actualType.IsAssignableTo(typeof(IEnumerable))) {
    //   var constructor = actualType.GetConstructor(BindingFlags.Public | BindingFlags.Instance, typeof());
    //   var value = ReadArray(actualType.GetGenericArguments()[0]);
    //   return constructor.Invoke([value]);
    // }

    // Custom type - use constructor
    return DeserializeObject(actualType);
  }


  private object DeserializeObject(Type type) {
    if (type == typeof(IOrigin)) {
      return DeserializeObject(typeof(SourceOrigin));
    }
    
    var constructorParams = new List<object>();
    var constructor = type.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)
      .Where(c => !c.IsPrivate && !c.GetParameters().Any(p => p.ParameterType.IsAssignableTo(typeof(Cloner))))
      .MaxBy(c =>
        c.GetCustomAttribute<ParseConstructorAttribute>() == null ? c.GetParameters().Length : int.MaxValue);
    var parameters = constructor.GetParameters();
    
    var ss1 = input.Substring(position);
    foreach (var parameter in parameters) {
      var ss = input.Substring(position);
      if (position < input.Length && input[position] == ',') {
        position++;
      }
      constructorParams.Add(DeserializeValue(parameter.ParameterType));
    }
    
    return constructor.Invoke(constructorParams.ToArray());
  }

  private static HashSet<Type> excludedTypes = [typeof(DafnyOptions)];

  private Array ReadArray(Type elementType) {
    var elements = new List<object>();

    while (position < input.Length && input[position] != ']') {
      var ss = input.Substring(position);
      if (elements.Count > 0) {
        if (input[position] != ',') {
          throw new Exception("Expected ',' in array");
        }

        position++;
      }

      elements.Add(DeserializeValue(elementType));
    }

    position++; // skip ']'

    Array array = Array.CreateInstance(elementType, elements.Count);
    for (int i = 0; i < elements.Count; i++) {
      array.SetValue(elements[i], i);
    }
    return array;
  }

  private string ReadString() {
    var sb = new StringBuilder();
    bool escaped = false;

    while (position < input.Length) {
      char c = input[position++];

      if (escaped) {
        switch (c) {
          case 'n': sb.Append('\n'); break;
          case 'r': sb.Append('\r'); break;
          case 't': sb.Append('\t'); break;
          default: sb.Append(c); break;
        }
        escaped = false;
      } else if (c == '\\') {
        escaped = true;
      } else if (c == '"') {
        break;
      } else {
        sb.Append(c);
      }
    }

    return sb.ToString();
  }

  private int ReadNumber() {
    string token = ReadToken();
    return int.Parse(token);
  }

  private string ReadToken() {
    var sb = new StringBuilder();
    while (position < input.Length && IsTokenChar(input[position])) {
      sb.Append(input[position++]);
    }
    return sb.ToString();
  }

  private string ReadUntil(char delimiter) {
    var sb = new StringBuilder();
    while (position < input.Length && input[position] != delimiter) {
      sb.Append(input[position++]);
    }
    return sb.ToString();
  }

  private bool TryMatch(string pattern) {
    if (position + pattern.Length > input.Length) {
      return false;
    }

    for (int i = 0; i < pattern.Length; i++) {
      if (input[position + i] != pattern[i]) {
        return false;
      }
    }

    if (pattern.Length > 0) {
      position += pattern.Length;
    }

    return true;
  }

  private void SkipWhitespace() {
    while (position < input.Length && char.IsWhiteSpace(input[position])) {
      position++;
    }
  }

  private bool IsTokenChar(char c) {
    return !char.IsWhiteSpace(c) && c != ',' && c != ']';
  }

  private bool IsSimpleType(Type type) {
    return type.IsPrimitive || type == typeof(string) || type == typeof(decimal)
        || type == typeof(DateTime) || Nullable.GetUnderlyingType(type) != null;
  }

  private object ConvertSimpleType(string value, Type type) {
    if (type == typeof(bool)) {
      return bool.Parse(value);
    }

    if (type == typeof(int)) {
      return int.Parse(value);
    }

    if (type == typeof(long)) {
      return long.Parse(value);
    }

    if (type == typeof(float)) {
      return float.Parse(value);
    }

    if (type == typeof(double)) {
      return double.Parse(value);
    }

    if (type == typeof(decimal)) {
      return decimal.Parse(value);
    }

    if (type == typeof(DateTime)) {
      return DateTime.Parse(value);
    }

    throw new Exception($"Unsupported simple type: {type}");
  }
}
