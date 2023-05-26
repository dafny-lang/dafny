using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Policy;

namespace Microsoft.Dafny.LanguageServer.Language;

class ByteArrayEquality : IEqualityComparer<byte[]> {
  public int Compare(byte[]? x, byte[]? y) {
    return (x, y) switch {
      (null, null) => 0,
      (null, _) => 1,
      (_, null) => -1,
      _ => x.SequenceEqual(y) ? 0 : 1
    };
  }

  public bool Equals(byte[]? x, byte[]? y) {
    return (x, y) switch {
      (null, null) => true,
      (null, _) => false,
      (_, null) => false,
      _ => x.SequenceEqual(y)
    };
    ;
  }

  public int GetHashCode(byte[] obj) {
    return BitConverter.ToInt32(obj, 0);
  }
}