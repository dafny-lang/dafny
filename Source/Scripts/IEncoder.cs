using System.Numerics;

namespace Scripts;

public interface IEncoder {
  void WriteNullable(bool isNull);
  void WriteInt(BigInteger value);
  void WriteQualifiedName(string name);
  void WriteString(string value);
  void WriteBool(bool value);
}