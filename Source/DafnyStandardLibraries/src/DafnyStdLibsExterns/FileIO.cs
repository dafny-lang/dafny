/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

namespace DafnyStdLibsExterns {
  using System;
  using System.IO;

  using Dafny;

  public class FileIO {
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
    public static void INTERNAL_ReadBytesFromFile(ISequence<char> path, out bool isError, out ISequence<byte> bytesRead,
      out ISequence<char> errorMsg) {
      isError = true;
      bytesRead = Sequence<byte>.Empty;
      errorMsg = Sequence<char>.Empty;
      try {
        bytesRead = Helpers.SeqFromArray(File.ReadAllBytes(path?.ToString()));
        isError = false;
      } catch (Exception e) {
        errorMsg = Helpers.SeqFromArray(e.ToString().ToCharArray());
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
    public static void INTERNAL_WriteBytesToFile(ISequence<char> path, ISequence<byte> bytes, out bool isError, out ISequence<char> errorMsg) {
      isError = true;
      errorMsg = Sequence<char>.Empty;
      try {
        string pathStr = path?.ToString();
        CreateParentDirs(pathStr);
        File.WriteAllBytes(pathStr, bytes.CloneAsArray());
        isError = false;
      } catch (Exception e) {
        errorMsg = Helpers.SeqFromArray(e.ToString().ToCharArray());
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
