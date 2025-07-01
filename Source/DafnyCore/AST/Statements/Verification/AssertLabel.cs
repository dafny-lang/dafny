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

  // Simplest approach for issue #6268: Don't clone AssertLabel objects at all
  public AssertLabel Clone(Cloner cloner) {
    // AssertLabel objects should maintain their identity across cloning
    // The E field gets filled during Boogie generation, so we need the same object
    // to be accessible from both AssertStmt and HideRevealStmt
    return this;  // Return the same object, don't create a new one
  }
}