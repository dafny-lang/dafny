using System;
using System.IO;

namespace Microsoft.Dafny;

public interface IOrigin : Microsoft.Boogie.IToken, IComparable<IOrigin> {

  bool IsInherited(ModuleDefinition m);

  bool InclusiveEnd { get; }
  bool IncludesRange { get; }
  /*
  int kind { get; set; }
  int pos { get; set; }
  int col { get; set; }
  int line { get; set; }
  string val { get; set; }
  bool IsValid { get; }*/
  string Boogie.IToken.filename {
    get => Uri == null ? null : Path.GetFileName(Uri.LocalPath);
    set => throw new NotSupportedException();
  }

  public string ActualFilename => Uri.LocalPath;
  string Filepath => Uri.LocalPath;

  Uri Uri { get; set; }

  Token StartToken { get; }
  Token EndToken { get; }

  /// <summary>
  /// TrailingTrivia contains everything after the token,
  /// until and including two newlines between which there is no commment
  /// All the remaining trivia is for the LeadingTrivia of the next token
  ///
  /// ```
  /// const /*for const*/ x /*for x*/ := /* for := */ 1/* for 1 */
  /// // for 1 again
  /// // for 1 again
  ///
  /// // Two newlines, now all the trivia is for var y
  /// // this line as well.
  /// var y := 2
  /// ```
  /// </summary>
  string TrailingTrivia { get; set; }
  string LeadingTrivia { get; set; }
  Token Next { get; set; } // The next token
  Token Prev { get; set; } // The previous token

  public IOrigin WithVal(string val);  // create a new token by setting the given val.

  bool IsCopy { get; }
}