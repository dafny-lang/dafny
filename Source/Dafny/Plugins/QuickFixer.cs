using System.Runtime.CompilerServices;
using System.Threading;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Plugins;

public interface IQuickFixInput {
  /// <summary>
  /// The URI of the document being considered
  /// </summary>
  string Uri { get; }
  /// <summary>
  /// The version of the document being considered. Always increasing
  /// If it did not change, it guarantees that Code is the same.
  /// This might be helpful for caching any pre-computation.
  /// </summary>
  int Version { get; }
  string Code { get; }
  [CanBeNull] Program Program { get; }
}

/// <summary>
/// Plugins implement one or more QuickFixer to offer "quick code fixes",
/// They should return very quickly, so most of the processing has to be done in the GetEdit()
/// </summary>
public abstract class QuickFixer {
  /// <summary>
  /// Returns the quick fixes associated to the provided selection, which could be a RangeToken
  /// </summary>
  /// <param name="input">The code, the program if parsed (and possibly resolved), and other data</param>
  /// <param name="selection">The current selection</param>
  /// <returns>A list of potential quickfixes</returns>
  public abstract QuickFix[] GetQuickFixes(IQuickFixInput input, IToken selection);
}

public abstract class QuickFix {
  // The title to display in the quickfix interface
  public string Title;
  // Edits are all performed at the same time
  // They are lazily invoked, so that they can be as complex as needed.
  public abstract QuickFixEdit[] GetEdits();
}

// This class enables returning quick fixes instantly.
public class InstantQuickFix : QuickFix {
  private readonly QuickFixEdit[] edits;

  public InstantQuickFix(string title, QuickFixEdit[] edits) {
    this.Title = title;
    this.edits = edits;
  }
  public override QuickFixEdit[] GetEdits() {
    return edits;
  }
}

/// <summary>
/// A quick fix replaces a range (represented as a token) with the replacing text.
/// </summary>
/// <param name="token">The range to replace. The start is given by the token's start, and the length is given by the val's length.</param>
/// <param name="replaceWith"></param>
public record QuickFixEdit(IToken token, string replaceWith = "");

public static class TokenExtensions {
  /// <summary>
  /// Get the virtual token corresponding to the start of a token
  /// </summary>
  public static IToken Start(this IToken token) {
    return new Token() {
      pos = token.pos,
      line = token.line,
      col = token.col,
      val = ""
    };
  }

  /// <summary>
  /// Get the virtual token corresponding to the start of a token
  /// Use only for the QuickFix
  /// </summary>
  public static IToken End(this IToken token) {
    return new Token {
      pos = token.pos + token.val.Length,
      line = token.line,
      col = token.col + token.val.Length,
      val = ""
    };
  }
}