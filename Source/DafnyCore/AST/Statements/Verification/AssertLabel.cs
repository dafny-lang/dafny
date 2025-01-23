using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssertLabel : Label {

  [FilledInDuringTranslation]
  public Boogie.Expr E;

  public AssertLabel(IOrigin tok, string label)
    : base(tok, label) {
    Contract.Requires(tok != null);
    Contract.Requires(label != null);
  }
}