using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using Newtonsoft.Json.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer;
public class ErrorMessageDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    DafnyDiagnostic diagnostic, Range selection) {
    var actionSigs = ErrorRegistry.GetAction(diagnostic.ErrorId);
    var actions = new List<DafnyCodeAction>();
    if (actionSigs != null) {
      var range = diagnostic.Token.ToRange();
      foreach (var sig in actionSigs) {
        var dafnyActions = sig(range);
        actions.AddRange(dafnyActions.Select(dafnyAction => new InstantDafnyCodeAction(dafnyAction.Title, new[] { diagnostic.ToLspDiagnostic() }, dafnyAction.Edits)));
      }
    }
    return actions;
  }
}