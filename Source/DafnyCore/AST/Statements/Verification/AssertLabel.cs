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
    // Respects clone contract by creating new objects, but ensures that
    // multiple references to the same original AssertLabel get the same clone
    return cloner.GetOrCreateAssertLabelClone(this);
  }
}