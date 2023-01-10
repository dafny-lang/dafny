using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Describe a single suggestion made to the user, where edits can be
/// computed lazily.
/// If the edits can be provided instantly, you can use the derived class
/// `new InstantDafnyCodeAction(title, edits)`
/// </summary>
public abstract class DafnyCodeAction {
  // The title to display in the quickfix interface
  public readonly string Title;

  public readonly Container<Diagnostic> Diagnostics;

  protected DafnyCodeAction(string title) {
    Title = title;
    Diagnostics = new();
  }

  protected DafnyCodeAction(string title, Container<Diagnostic> diagnostics) {
    Title = title;
    Diagnostics = diagnostics;
  }

  // Edits are all performed at the same time
  // They are lazily invoked, so that they can be as complex as needed.
  public abstract IEnumerable<DafnyCodeActionEdit> GetEdits();
}

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

/// <summary>
/// A quick fix replaces a range with the replacing text.
/// </summary>
/// <param name="Range">The range to replace. The start is given by the token's start, and the length is given by the val's length.</param>
/// <param name="Replacement"></param>
public record DafnyCodeActionEdit(Range Range, string Replacement = "");


