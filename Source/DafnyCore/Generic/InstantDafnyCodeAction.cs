using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Plugins;

// This class enables returning code actions instantly.
public class InstantDafnyCodeAction : DafnyCodeAction {
  private readonly DafnyCodeActionEdit[] edits;

  public InstantDafnyCodeAction(string title, DafnyCodeActionEdit[] edits) : base(title) {
    this.edits = edits;
  }
  public InstantDafnyCodeAction(string title, Container<Diagnostic> diagnostics, DafnyCodeActionEdit[] edits) : base(title, diagnostics) {
    this.edits = edits;
  }
  public override DafnyCodeActionEdit[] GetEdits() {
    return edits;
  }
}
