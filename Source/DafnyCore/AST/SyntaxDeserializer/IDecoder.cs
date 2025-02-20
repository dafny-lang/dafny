using System.IO;

namespace Microsoft.Dafny;

public interface IDecoder {
  string Position { get; }
  int ReadInt32();
  bool ReadBool();
  bool ReadIsNull();
  string ReadString();
  string ReadQualifiedName();
}