using System.Numerics;
using System.Text;
using Microsoft.BaseTypes;

namespace Scripts;

class TextEncoder(StringBuilder writer) : IEncoder {
  public void WriteNullable(bool isNull) {
    if (isNull) {
      writer.Append("null");
      writer.Append(' ');
    }
  }

  public void WriteBool(bool value) {
    writer.Append(value ? "true" : "false");
    writer.Append(' ');
  }

  public void WriteBigDec(BigDec bigDec) {
    writer.Append(bigDec.ToString());
    writer.Append(";");
    writer.Append(' ');
  }

  public void WriteInt(BigInteger value) {
    writer.Append(value);
    writer.Append(";");
    writer.Append(' ');
  }

  public void WriteQualifiedName(string name) {
    writer.Append(name);
    writer.Append(' ');
  }

  public void WriteString(string value) {
    writer.Append(EscapeString(value));
    writer.Append(' ');
  }

  private static string EscapeString(string str) {
    var sb = new StringBuilder("\"");
    foreach (char c in str) {
      switch (c) {
        case '"':
          sb.Append("\\\"");
          break;
        case '\\':
          sb.Append("\\\\");
          break;
        case '\n':
          sb.Append("\\n");
          break;
        case '\r':
          sb.Append("\\r");
          break;
        case '\t':
          sb.Append("\\t");
          break;
        default:
          sb.Append(c);
          break;
      }
    }
    sb.Append("\"");
    return sb.ToString();
  }
}