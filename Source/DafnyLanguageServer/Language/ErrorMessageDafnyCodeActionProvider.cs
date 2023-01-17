using System;
using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;
using Microsoft.Dafny.LanguageServer.Plugins;
using Newtonsoft.Json.Linq;
using Microsoft.Dafny.LanguageServer.Handlers;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny.LanguageServer;
public class ErrorMessageDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {
  private Range InterpretDataAsRangeOrDefault(JToken? data, Range def) {
    if (data is null) {
      return def;
    }
    // If the token provided does not have the format expected, just use the default
    try {
      var sl = data.First?.First?.First?.ToString();
      var sc = data.First?.First?.Last?.ToString();
      var el = data.Last?.First?.First?.ToString();
      var ec = data.Last?.First?.Last?.ToString();
      if (sl == null || sc == null || el == null || ec == null) {
        return def;
      } else {
        int sline = Int32.Parse(sl.Substring(sl.IndexOf(":") + 1));
        int schar = Int32.Parse(sc.Substring(sc.IndexOf(":") + 1));
        int eline = Int32.Parse(el.Substring(el.IndexOf(":") + 1));
        int echar = Int32.Parse(ec.Substring(ec.IndexOf(":") + 1));
        return new Range(sline, schar, eline, echar);
      }
    } catch (Exception) {
    }
    return def;
  }

  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input, Diagnostic diagnostic, Range selection) {
    ErrorID errorID = ErrorID.None;
    bool ok = Enum.TryParse<ErrorID>(diagnostic.Code, out errorID);
    var action = DafnyCodeActions.GetAction(errorID);
    if (action == null) {
      return new List<DafnyCodeAction> { };
    } else {
      Range range = InterpretDataAsRangeOrDefault(diagnostic.Data, diagnostic.Range);
      return action(diagnostic, range);
    }
  }
}