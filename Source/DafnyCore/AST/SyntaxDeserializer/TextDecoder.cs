using System;
using System.Text;
using Microsoft.BaseTypes;

namespace Microsoft.Dafny;

/// <summary>
/// A textual serialization format can be used to make it easier to debug serialization issues
/// </summary>
public class TextDecoder(string input) : IDecoder {
  private const int IntStopCharacter = ';';
  private int position;

  public string Position => position.ToString();
  public string Input => input;

  public int ReadInt32() {
    return int.Parse(GetNumberChars());
  }

  private string GetNumberChars() {
    var start = position;
    while (position < input.Length && input[position] != IntStopCharacter) {
      position++;
    }

    var end = position;
    position++;

    ReadSeparator();
    string chars = input.Substring(start, end - start);
    return chars;
  }

  private void ReadSeparator() {
    if (input[position] != ' ') {
      throw Error("a space");
    }

    position++;
  }

  private Exception Error(string expectation) {
    throw new Exception($"Expected {expectation} at {position} but found " +
                        $"{Remainder.Substring(0, Math.Max(Remainder.Length, 5))}");
  }

  public bool ReadBool() {
    if (CheckAndAdvance("true")) {
      return true;
    }
    if (CheckAndAdvance("false")) {
      return false;
    }

    throw Error("true or false");
  }

  public bool ReadIsNull() {
    return CheckAndAdvance("null");
  }

  private bool CheckAndAdvance(string keyword) {
    if (position + keyword.Length <= input.Length && input.Substring(position, keyword.Length) == keyword) {
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
      throw Error("a quotation mark");
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

  public long ReadInt64() {
    return long.Parse(GetNumberChars());
  }

  public short ReadInt16() {
    return short.Parse(GetNumberChars());
  }

  public BigDec ReadBigDec() {
    return BigDec.FromString(GetNumberChars());
  }
}