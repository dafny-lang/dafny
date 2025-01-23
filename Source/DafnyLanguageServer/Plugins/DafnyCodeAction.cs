using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

/// <summary>
/// Describe a single suggestion made to the user, where edits can be
/// computed lazily.
/// If the edits can be provided instantly, you can use the derived class
/// `new InstantDafnyCodeAction(title, edits)`
/// </summary>
public abstract class DafnyCodeAction(string title, Container<Diagnostic> diagnostics) {
  // The title to display in the quickfix interface
  public readonly string Title = title;

  public readonly Container<Diagnostic> Diagnostics = diagnostics;

  protected DafnyCodeAction(string title) : this(title, new()) {
  }

  // Edits are all performed at the same time
  // They are lazily invoked, so that they can be as complex as needed.
  public abstract IEnumerable<DafnyCodeActionEdit> GetEdits();
}