using System.Numerics;
using Microsoft.BaseTypes;

namespace Scripts;

public interface IEncoder {
  void WriteNullable(bool isNull);
  void WriteInt(BigInteger value);
  void WriteQualifiedName(string name);
  void WriteString(string value);
  void WriteBool(bool value);
  void WriteBigDec(BigDec bigDec);
}