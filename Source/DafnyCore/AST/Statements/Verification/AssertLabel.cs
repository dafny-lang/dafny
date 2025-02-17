using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssertLabel : Label {

  [FilledInDuringTranslation]
  public Boogie.Expr E;

  public AssertLabel(IOrigin tok, string name)
    : base(tok, name) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
  }
}