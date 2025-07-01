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
    // Uses standard cloning pattern consistent with other clone dictionaries
    return cloner.CloneAssertLabel(this);
  }
}