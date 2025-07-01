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
    // Use the cloner's shared AssertLabel mapping to ensure that multiple references
    // to the same label name get the same cloned AssertLabel object
    return cloner.GetOrCreateAssertLabelClone(this);
  }
}