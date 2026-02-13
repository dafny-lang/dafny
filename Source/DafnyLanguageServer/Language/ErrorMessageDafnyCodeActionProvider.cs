using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer;
public class ErrorMessageDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    Diagnostic diagnostic, Range selection) {
    if (diagnostic.Code is not { IsString: true }) {
      return [];
    }
    var actionSigs = ErrorRegistry.GetAction(diagnostic.Code.Value.String);
    var actions = new List<DafnyCodeAction>();
    if (actionSigs != null) {
      var range = FindTokenRangeFromLspRange(input, diagnostic.Range, false);
      if (range == null) {
        return actions;
      }
      foreach (var sig in actionSigs) {
        var dafnyActions = sig(range);
        actions.AddRange(dafnyActions.Select(dafnyAction => new InstantDafnyCodeAction(dafnyAction.Title, new[] { diagnostic }, dafnyAction.Edits)));
      }
    }
    return actions;
  }

  public ErrorMessageDafnyCodeActionProvider(ILogger<DafnyCodeActionHandler> logger) : base(logger) {
  }
}