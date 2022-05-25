using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Plugins implement one or more QuickFixer to offer "quick code fixes",
/// They should return very quickly, so most of the processing has to be done in the GetEdit()
/// of every QuickFix.
///
/// To provide quick fixes for diagnostics related to the selection,
/// implement the subclass 'DiagnosticQuickFixer'
///
/// To convert a token to a LSP Range include `using Microsoft.Dafny.LanguageServer.Language;`
/// and use `token.GetLspRange()`
///
/// To get the start or end of a range as another range, use
///   QuickFixerHelpers.GetStartRange(range) or ``range.GetStartRange()`
/// </summary>
public abstract class QuickFixer {
  /// <summary>
  /// Returns the quick fixes associated to the provided selection, which could be a RangeToken
  /// </summary>
  /// <param name="input">The code, the program if parsed (and possibly resolved), and other data</param>
  /// <param name="selection">The current selection</param>
  /// <returns>A list of potential quickfixes, possibly computed lazily</returns>
  public abstract QuickFix[] GetQuickFixes(IQuickFixInput input, Range selection);
}

/// <summary>
/// Implement this class if you need to compute quick fixes only for the diagnostics
/// that are being touched by the selection
/// </summary>
public abstract class DiagnosticQuickFixer : QuickFixer {
  public override QuickFix[] GetQuickFixes(IQuickFixInput input, Range selection) {
    if (input.Program == null) {
      return new QuickFix[] { };
    }
    var diagnostics = input.Diagnostics;
    var result = new List<QuickFix>() { };
    foreach (var diagnostic in diagnostics) {
      if (diagnostic.Range.Start.Line <= selection.Start.Line &&
          selection.Start.Line <= diagnostic.Range.End.Line) {
        var moreQuickFixes = GetQuickFixes(input, diagnostic, selection);
        if (moreQuickFixes != null) {
          result.AddRange(moreQuickFixes);
        }
      }
    }

    return result.ToArray();
  }

  /// <summary>
  /// You can safely assume that input.Program is not null
  /// </summary>
  /// <param name="input"></param>
  /// <param name="diagnostic"></param>
  /// <param name="selection"></param>
  /// <returns></returns>
  protected abstract IEnumerable<QuickFix>? GetQuickFixes(IQuickFixInput input, Diagnostic diagnostic, Range selection);
}
