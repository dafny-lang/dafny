#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny;

partial class Deserializer(Uri uri, string input) {
  private int position;

  private List<T> DeserializeList<T>() {
    return DeserializeArray<T>().ToList();
  }

  public Token DeserializeToken()
  {
    var parameter0 = DeserializeGeneric<Int32>();
    var parameter1 = DeserializeGeneric<Int32>();
    return new Token(parameter0, parameter1) {
      Uri = uri
    };
  }

  private T[] DeserializeArray<T>() {
    var elements = new List<object>();

    while (position < input.Length && input[position] != ']') {
      var ss = input.Substring(position);
      if (elements.Count > 0) {
        if (input[position] != ',') {
          throw new Exception("Expected ',' in array");
        }

        position++;
      }

      elements.Add(Value<T>());
    }

    position++; // skip ']'
    SkipComma();

    var array = new T[elements.Count];
    for (int i = 0; i < elements.Count; i++) {
      array.SetValue(elements[i], i);
    }
    return array;
  }

  private T Value<T>() {
    return DeserializeGeneric<T>();
  }

  private string DeserializeString() {
    if (!TryMatch("\"")) {
      throw new Exception();
    }
    
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

    SkipComma();
    return sb.ToString();
  }

  private void SkipComma()
  {
    if (position < input.Length && input[position] == ',') {
      position++;
    }
  }

  public string Remainder => input.Substring(position);
  
  private int DeserializeInt32() {
    string token = ReadToken();
    return int.Parse(token);
  }

  private object DeserializeObject() {
    return DeserializeGeneric<object>();
  }

  public T DeserializeGeneric<T>() {
    if (TryMatch("null")) {
      SkipComma();
      return default;
    }
    
    var actualType = typeof(T);
    if (TryMatch("+")) {
      string typeName = ReadUntil(':');
      actualType = System.Type.GetType("Microsoft.Dafny." + typeName) ??
                   System.Type.GetType("System." + typeName) ?? throw new Exception($"Type not found: {typeName}");
      position++; // skip ':'
    }

    if (actualType == typeof(string)) {
      return (T)(object)DeserializeString();
    }
    
    if (IsSimpleType(actualType)) {
      return (T)ConvertSimpleType(ReadToken(), actualType);
    }

    if (actualType == typeof(IOrigin)) {
      return (T)(object)DeserializeSourceOrigin();
    }

    return (T)DeserializeObject(actualType);
  }

  private string ReadToken() {
    var sb = new StringBuilder();
    while (position < input.Length && IsTokenChar(input[position])) {
      sb.Append(input[position++]);
    }
    SkipComma();
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

  private bool IsSimpleType(System.Type type) {
    return type.IsPrimitive || type == typeof(string) || type == typeof(decimal)
           || type == typeof(DateTime) || Nullable.GetUnderlyingType(type) != null;
  }

  private object ConvertSimpleType(string value, System.Type type) {
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
  
  private bool DeserializeBoolean() {
    var token = ReadToken();
    return bool.Parse(token);
  }
}