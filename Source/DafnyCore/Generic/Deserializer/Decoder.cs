using System;
using System.IO;
using System.Text;

namespace Microsoft.Dafny;

public interface IDecoder {
  string Position { get; }
  int ReadInt32();
  bool ReadBool();
  bool ReadIsNull();
  string ReadString();
  string ReadQualifiedName();
}

public class TextDecoder(string input) : IDecoder {
  private const int IntStopCharacter = ';';
  private int position;

  public string Position => position.ToString();
  public string Input => input;

  public int ReadInt32() {
    var start = position;
    while (position < input.Length && input[position] != IntStopCharacter) {
      position++;
    }

    var end = position;
    position++;

    ReadSeparator();
    string chars = input.Substring(start, end - start);
    return int.Parse(chars);
  }

  private void ReadSeparator() {
    if (input[position] != ' ') {
      throw new Exception();
    }

    position++;
  }

  public bool ReadBool() {
    if (CheckAndAdvance("true")) {
      return true;
    }
    if (CheckAndAdvance("false")) {
      return false;
    }

    throw new Exception();
  }

  public bool ReadIsNull() {
    return CheckAndAdvance("null");
  }

  private bool CheckAndAdvance(string keyword) {
    if (input.Substring(position, keyword.Length) == keyword) {
      position += keyword.Length;
      ReadSeparator();
      return true;
    }

    return false;
  }

  public string Remainder => input.Substring(position);

  public string ReadString() {
    var sb = new StringBuilder();
    bool escaped = false;

    if (input[position] != '"') {
      throw new Exception();
    }

    position++;

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

    ReadSeparator();
    return sb.ToString();
  }

  public string ReadQualifiedName() {
    var start = position;
    while (position < input.Length) {
      var c = input[position];
      if (!char.IsLetterOrDigit(c) && c != '.') {
        break;
      }
      position++;
    }
    var end = position;
    ReadSeparator();
    return input.Substring(start, end - start);
  }
}