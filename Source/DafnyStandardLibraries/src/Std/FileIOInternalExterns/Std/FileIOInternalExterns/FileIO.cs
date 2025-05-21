/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

namespace Std.FileIOInternalExterns {
  using System;
  using System.IO;

  using Dafny;

  public class __default {
    /// <summary>
    /// Attempts to read all bytes from the file at the given path, and outputs the following values:
    /// <list>
    ///   <item>
    ///     <term>isError</term>
    ///     <description>
    ///       true iff an exception was thrown during path string conversion or when reading the file
    ///     </description>
    ///   </item>
    ///   <item>
    ///     <term>bytesRead</term>
    ///     <description>
    ///       the sequence of bytes read from the file, or an empty sequence if <c>isError</c> is true
    ///     </description>
    ///   </item>
    ///   <item>
    ///     <term>errorMsg</term>
    ///     <description>
    ///       the error message of the thrown exception if <c>isError</c> is true, or an empty sequence otherwise
    ///     </description>
    ///   </item>
    /// </list>
    ///
    /// We output these values individually because Result is not defined in the runtime but instead in library code.
    /// It is the responsibility of library code to construct an equivalent Result value.
    /// </summary>
    public static void INTERNAL__ReadBytesFromFile(ISequence<Dafny.Rune> path, out bool isError, out ISequence<byte> bytesRead,
      out ISequence<Dafny.Rune> errorMsg) {
      isError = true;
      bytesRead = Sequence<byte>.Empty;
      errorMsg = Sequence<Rune>.Empty;
      try {
        bytesRead = Helpers.SeqFromArray(File.ReadAllBytes(path?.ToVerbatimString(false)));
        isError = false;
      } catch (Exception e) {
        errorMsg = Sequence<Rune>.UnicodeFromString(e.ToString());
      }
    }

    /// <summary>
    /// Attempts to write all given bytes to the file at the given path, creating nonexistent parent directories as necessary,
    /// and outputs the following values:
    /// <list>
    ///   <item>
    ///     <term>isError</term>
    ///     <description>
    ///       true iff an exception was thrown during path string conversion or when writing to the file
    ///     </description>
    ///   </item>
    ///   <item>
    ///     <term>errorMsg</term>
    ///     <description>
    ///       the error message of the thrown exception if <c>isError</c> is true, or an empty sequence otherwise
    ///     </description>
    ///   </item>
    /// </list>
    ///
    /// We output these values individually because Result is not defined in the runtime but instead in library code.
    /// It is the responsibility of library code to construct an equivalent Result value.
    /// </summary>
    public static void INTERNAL__WriteBytesToFile(ISequence<Dafny.Rune> path, ISequence<byte> bytes, out bool isError, out ISequence<Dafny.Rune> errorMsg) {
      isError = true;
      errorMsg = Sequence<Rune>.Empty;
      try {
        string pathStr = path?.ToVerbatimString(false);
        CreateParentDirs(pathStr);
        File.WriteAllBytes(pathStr, bytes.CloneAsArray());
        isError = false;
      } catch (Exception e) {
        errorMsg = Sequence<Rune>.UnicodeFromString(e.ToString());
      }
    }

    /// <summary>
    /// Creates the nonexistent parent directory(-ies) of the given path.
    /// </summary>
    private static void CreateParentDirs(string path) {
      string parentDir = Path.GetDirectoryName(Path.GetFullPath(path));
      Directory.CreateDirectory(parentDir);
    }
  }
}
