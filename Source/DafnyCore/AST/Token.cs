#nullable enable
using System;
using System.IO;

namespace Microsoft.Dafny;

/// <summary>
/// Has one-indexed line and column fields
/// </summary>
public class Token : IOrigin {

  public Token? peekedTokens; // Used only internally by Coco when the scanner "peeks" tokens. Normally null at the end of parsing
  public static readonly Token NoToken = new();
  public static readonly Token Cli = new(-1, -1);
  public static readonly Token Ide = new(1, 1);
  public string filename => Path.GetFileName(Filepath);

  public Token() : this(0, 0) { }

  [SyntaxConstructor]
  public Token(int line, int col) {
    this.line = line;
    this.col = col;
    this.val = "";
  }

  public bool IsSourceToken => this != NoToken;
  public int kind { get; set; } // Used by coco, so we can't rename it to Kind

  public bool IsInherited(ModuleDefinition m) {
    return false;
  }
  public bool IncludesRange => false;
  public string ActualFilename => Filepath;
  public string Filepath => Uri?.LocalPath!;
  public Uri Uri { get; set; } = null!;
  public TokenRange? EntireRange => null;
  public TokenRange ReportingRange => new TokenRange(this, this);

  public int pos { get; set; } // Used by coco, so we can't rename it to Pos

  /// <summary>
  /// One-indexed
  /// </summary>
  public int col { get; set; } // Used by coco, so we can't rename it to Col

  /// <summary>
  /// One-indexed
  /// </summary>
  public int line { get; set; } // Used by coco, so we can't rename it to Line

  public string val { get; set; } // Used by coco, so we can't rename it to Val

  public string LeadingTrivia { get; set; } = "";


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
  public string TrailingTrivia { get; set; } = "";

  public Token Next { get; set; } = null!; // The next token

  public Token Prev { get; set; } = null!; // The previous token

  // ReSharper disable once ConditionIsAlwaysTrueOrFalseAccordingToNullableAPIContract
  public bool IsValid => this.ActualFilename != null;

  public SourceOrigin To(Token end) => new(this, end);

  public IOrigin WithVal(string newVal) {
    return new Token {
      pos = pos,
      col = col,
      line = line,
      Prev = Prev,
      Next = Next,
      Uri = Uri,
      kind = kind,
      val = newVal
    };
  }

  public bool IsCopy => false;

  public int CompareTo(Boogie.IToken? other) {
    if (other == null) {
      return 1;
    }
    if (line != other.line) {
      return line.CompareTo(other.line);
    }
    return col.CompareTo(other.col);
  }

  public override int GetHashCode() {
    return pos;
  }

  public override string ToString() {
    return $"'{val}': {Path.GetFileName(Filepath)}@{pos} - @{line}:{col}";
  }

  public int CompareTo(IOrigin other) {
    if (line != other.line) {
      return line.CompareTo(other.line);
    }
    return col.CompareTo(other.col);
  }
}
