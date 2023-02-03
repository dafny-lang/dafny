using System;
using System.Collections.Concurrent;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Plugins;
using Newtonsoft.Json.Linq;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny.LanguageServer.Handlers;

public class DafnyCodeActions {

  private static Dictionary<ErrorID, Func<Diagnostic, Range, List<DafnyCodeAction>>> codeActionMap =
    new Dictionary<ErrorID, Func<Diagnostic, Range, List<DafnyCodeAction>>>();

  public static Func<Diagnostic, Range, List<DafnyCodeAction>>? GetAction(ErrorID errorId) {
    init();
    return codeActionMap.ContainsKey(errorId) ? codeActionMap[errorId] : null;
  }

  public static List<DafnyCodeAction> ReplacementAction(string title, Diagnostic diagnostic, Range range, string newText) {
    var edit = new DafnyCodeActionEdit[] { new DafnyCodeActionEdit(range, newText) };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  public static List<DafnyCodeAction> RemoveAction(string title, Diagnostic diagnostic, Range range) {
    var edit = new DafnyCodeActionEdit[] { new DafnyCodeActionEdit(range, "") };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  private static bool initialized = false;
  public static void init() {
    if (initialized) {
      return;
    }
    initialized = true;
    codeActionMap.Add(ErrorID.p_bad_const_initialize_op, (Diagnostic diagnostic, Range range) => ReplacementAction("replace = with :=", diagnostic, range, ":="));
    codeActionMap.Add(ErrorID.p_abstract_not_allowed, (Diagnostic diagnostic, Range range) => RemoveAction("remove 'abstract'", diagnostic, range));
    codeActionMap.Add(ErrorID.p_no_leading_underscore, (Diagnostic diagnostic, Range range) => RemoveAction("remove underscore", diagnostic, range));

  }
}


