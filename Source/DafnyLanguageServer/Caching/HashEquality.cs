using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Policy;

namespace Microsoft.Dafny.LanguageServer.Language;

/// <summary>
/// Useful for using hashes as keys in dictionaries
/// </summary>
public class HashEquality : IEqualityComparer<byte[]> {
  public bool Equals(byte[]? x, byte[]? y) {
    return (x, y) switch {
      (null, null) => true,
      (null, _) => false,
      (_, null) => false,
      _ => x.SequenceEqual(y)
    };
  }

  /// <summary>
  /// Since the bytes themselves are already a hash,
  /// we don't expect ot gain a benefit from hashing those bytes into 32 bits
  /// over simply taking the first 32 bits of the original hash.
  /// </summary>
  public int GetHashCode(byte[] obj) {
    if (obj.Length == 0) {
      return 0;
    }
    return BitConverter.ToInt32(obj, 0);
  }
}