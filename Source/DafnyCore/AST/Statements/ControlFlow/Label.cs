using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Label {
  public IOrigin Tok;
  public string Name;
  string uniqueId = null;

  public string AssignUniqueId(FreshIdGenerator idGen) {
    if (uniqueId == null) {
      uniqueId = idGen.FreshNumericId("label");
    }
    return uniqueId;
  }
  public Label(IOrigin tok, string/*?*/ name) {
    Contract.Requires(tok != null);
    Tok = tok;
    Name = name;
  }
}