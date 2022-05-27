using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Describe a single suggestion made to the user, where edits can be
/// computed lazily.
/// If the edits can be provided instantly, you can use the derived class
/// `new InstantQuickFix(title, edits)`
/// </summary>
public abstract class QuickFix {
  // The title to display in the quickfix interface
  public string Title;

  protected QuickFix(string title) {
    Title = title;
  }

  // Edits are all performed at the same time
  // They are lazily invoked, so that they can be as complex as needed.
  public abstract QuickFixEdit[] GetEdits();
}

// This class enables returning quick fixes instantly.
public class InstantQuickFix : QuickFix {
  private readonly QuickFixEdit[] edits;

  public InstantQuickFix(string title, QuickFixEdit[] edits) : base(title) {
    this.edits = edits;
  }
  public override QuickFixEdit[] GetEdits() {
    return edits;
  }
}

/// <summary>
/// A quick fix replaces a range with the replacing text.
/// </summary>
/// <param name="Range">The range to replace. The start is given by the token's start, and the length is given by the val's length.</param>
/// <param name="Replacement"></param>
public record QuickFixEdit(Range Range, string Replacement = "");
