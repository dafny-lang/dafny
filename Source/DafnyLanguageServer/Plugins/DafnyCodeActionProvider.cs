using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Plugins implement one or more DafnyCodeActionProvider to offer "quick code fixes".
/// They should return very quickly, so most of the processing has to be done in the GetEdit()
/// of every DafnyCodeAction.
///
/// To provide code actions for diagnostics related to the selection,
/// implement the subclass 'DiagnosticDafnyCodeActionProvider'
///
/// To convert a token to an LSP Range include `using Microsoft.Dafny.LanguageServer.Language;`
/// and use `token.GetLspRange()`
///
/// To get the start or end of a range as another range, use
///   DafnyCodeActionProviderHelpers.GetStartRange(range) or `range.GetStartRange()`
/// </summary>
public abstract class DafnyCodeActionProvider {
  /// <summary>
  /// Returns the code actions associated to the provided selection, which could be a RangeToken
  /// </summary>
  /// <param name="input">The code, the program if parsed (and possibly resolved), and other data</param>
  /// <param name="selection">The current selection</param>
  /// <returns>Potential quickfixes</returns>
  public abstract IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection);
}

/// <summary>
/// Implement this class if you need to compute code actions only for the diagnostics
/// that are being touched by the selection
/// </summary>
public abstract class DiagnosticDafnyCodeActionProvider : DafnyCodeActionProvider {
  public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
    if (input.Program == null) {
      return System.Array.Empty<DafnyCodeAction>();
    }
    var diagnostics = input.Diagnostics;
    var result = new List<DafnyCodeAction>();
    foreach (var diagnostic in diagnostics) {
      var range = diagnostic.Token.GetLspRange();
      var linesOverlap = range.Start.Line <= selection.Start.Line
                         && selection.Start.Line <= range.End.Line;
      if (linesOverlap) {
        var moreDafnyCodeActions = GetDafnyCodeActions(input, diagnostic, selection);
        if (moreDafnyCodeActions != null) {
          result.AddRange(moreDafnyCodeActions);
        }
      }
    }

    return result;
  }

  /// <summary>
  /// Returns all code actions that can be applied to solve the given diagnostic
  /// </summary>
  /// <param name="input">The state of the document, containing the code and possibly the resolved program</param>
  /// <param name="dafnyDiagnostic"></param>
  /// <param name="selection">Where the user's caret is</param>
  protected abstract IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    DafnyDiagnostic diagnostic, Range selection);
}
