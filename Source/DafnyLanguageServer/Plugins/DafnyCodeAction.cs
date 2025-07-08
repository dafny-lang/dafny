using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

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