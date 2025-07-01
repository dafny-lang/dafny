using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssertLabel : Label, ICloneable<AssertLabel> {

  [FilledInDuringTranslation]
  public Boogie.Expr E;

  public AssertLabel(IOrigin tok, string name)
    : base(tok, name) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
  }

  // Proper cloning implementation for issue #6268
  public AssertLabel Clone(Cloner cloner) {
    return new AssertLabel(cloner, this);
  }

  public AssertLabel(Cloner cloner, AssertLabel original) : base(cloner.Origin(original.Tok), original.Name) {
    // PROPER FIX: Preserve the E field during cloning if it exists
    // This ensures that cloned AssertLabel objects maintain their connection
    // to the translated expressions filled during Boogie generation
    if (cloner.CloneResolvedFields && original.E != null) {
      E = original.E;
    }
  }
}