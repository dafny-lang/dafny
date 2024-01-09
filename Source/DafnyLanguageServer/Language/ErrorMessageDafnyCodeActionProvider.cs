using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer;
public class ErrorMessageDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    Diagnostic diagnostic, Range selection) {
    if (diagnostic.Code is not { IsString: true }) {
      return Enumerable.Empty<DafnyCodeAction>();
    }
    var actionSigs = ErrorRegistry.GetAction(diagnostic.Code.Value.String);
    var actions = new List<DafnyCodeAction>();
    if (actionSigs != null) {
      var range = FindTokenRangeFromLspRange(input, diagnostic.Range);
      foreach (var sig in actionSigs) {
        var dafnyActions = sig(range);
        actions.AddRange(dafnyActions.Select(dafnyAction => new InstantDafnyCodeAction(dafnyAction.Title, new[] { diagnostic }, dafnyAction.Edits)));
      }
    }
    return actions;
  }

  public static RangeToken FindTokenRangeFromLspRange(IDafnyCodeActionInput input, Range range) {
    var start = range.Start;
    var startNode = input.Program.FindNode<Node>(input.Uri.ToUri(), start.ToDafnyPosition());
    var startToken = startNode.CoveredTokens.First(t => t.line - 1 == start.Line && t.col - 1 == start.Character);
    var end = range.End;
    var endNode = input.Program.FindNode<Node>(input.Uri.ToUri(), end.ToDafnyPosition());
    var endToken = endNode.CoveredTokens.FirstOrDefault(t => t.line - 1 == end.Line && t.col - 1 + t.val.Length == end.Character);
    return new RangeToken(startToken, endToken);
  }
}