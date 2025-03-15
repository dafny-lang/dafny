using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
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

  // When building DafnyCodeActionEdit (what DafnyCodeAction return),
  // use this to create ranges suitable for insertion
  protected static TokenRange InsertBefore(Token tok) {
    return new TokenRange(tok, null);
  }

  protected static TokenRange Replace(Token tok) {
    return new TokenRange(tok, tok);
  }
  protected static TokenRange InsertAfter(IOrigin tok) {
    return new TokenRange(new Token(tok.line, tok.col + tok.val.Length) {
      pos = tok.pos + tok.val.Length,
    }, null);
  }
}

/// <summary>
/// Implement this class if you need to compute code actions only for the diagnostics
/// that are being touched by the selection
/// </summary>
public abstract class DiagnosticDafnyCodeActionProvider : DafnyCodeActionProvider {
  private ILogger<DafnyCodeActionHandler> logger;

  protected DiagnosticDafnyCodeActionProvider(ILogger<DafnyCodeActionHandler> logger) {
    this.logger = logger;
  }

  public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
    if (input.Program == null) {
      return System.Array.Empty<DafnyCodeAction>();
    }
    var diagnostics = input.Diagnostics;
    var result = new List<DafnyCodeAction>();
    var uri = input.Uri.ToUri();
    foreach (var diagnostic in diagnostics.Where(d => d.Uri == uri)) {
      var range = diagnostic.Diagnostic.Range;
      var linesOverlap = range.Start.Line <= selection.Start.Line
                         && selection.Start.Line <= range.End.Line;
      if (linesOverlap) {
        var moreDafnyCodeActions = GetDafnyCodeActions(input, diagnostic.Diagnostic, selection);
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
    Diagnostic diagnostic, Range selection);

  public TokenRange? FindTokenRangeFromLspRange(IDafnyCodeActionInput input, Range range, bool useNodeRange) {
    var start = range.Start;
    if (useNodeRange) {
      var node = input.Program.FindNode(input.Uri.ToUri(), start.ToDafnyPosition(), node =>
        node.EntireRange.ToLspRange().Contains(range.End));
      return node.EntireRange;
    }

    var startNode = input.Program.FindNode<Node>(input.Uri.ToUri(), start.ToDafnyPosition());
    if (startNode == null) {
      // A program should have FileModuleDefinition nodes whose ranges span the entire contents of files,
      // But currently those nodes are missing
      return null;
    }

    var startToken = startNode.CoveredTokens.FirstOrDefault(t => t.line - 1 == start.Line && t.col - 1 == start.Character);
    if (startToken == null) {
      logger.LogError($"Could not find starting token for position {start} in node {startNode}");
      return null;
    }
    var end = range.End;
    var endNode = input.Program.FindNode<Node>(input.Uri.ToUri(), end.ToDafnyPosition());
    var endToken = endNode.CoveredTokens.FirstOrDefault(t => t.line - 1 == end.Line && t.col - 1 + t.val.Length == end.Character);
    return new TokenRange(startToken, endToken);
  }
}
