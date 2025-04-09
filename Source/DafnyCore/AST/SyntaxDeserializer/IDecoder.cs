using System.IO;
using Microsoft.BaseTypes;

namespace Microsoft.Dafny;

public interface IDecoder {
  string Position { get; }
  int ReadInt32();
  bool ReadBool();
  bool ReadIsNull();
  string ReadString();
  string ReadQualifiedName();
  long ReadInt64();
  short ReadInt16();
  BigDec ReadBigDec();
}