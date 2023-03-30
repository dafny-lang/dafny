using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Plugins;

// This class enables returning code actions instantly.
public class InstantDafnyCodeAction : DafnyCodeAction {
  private readonly IReadOnlyList<DafnyCodeActionEdit> edits;

  public InstantDafnyCodeAction(string title, IReadOnlyList<DafnyCodeActionEdit> edits) : base(title) {
    this.edits = edits;
  }
  public InstantDafnyCodeAction(string title, Container<Diagnostic> diagnostics, IReadOnlyList<DafnyCodeActionEdit> edits) : base(title, diagnostics) {
    this.edits = edits;
  }
  public override IReadOnlyList<DafnyCodeActionEdit> GetEdits() {
    return edits;
  }
}
