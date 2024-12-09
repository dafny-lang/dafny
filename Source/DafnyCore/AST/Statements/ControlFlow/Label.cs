using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class Label {
  public readonly IOrigin Tok;
  public readonly string Name;
  string uniqueId = null;

  public string AssignUniqueId(FreshIdGenerator idGen) {
    if (uniqueId == null) {
      uniqueId = idGen.FreshNumericId("label");
    }
    return uniqueId;
  }
  public Label(IOrigin tok, string/*?*/ label) {
    Contract.Requires(tok != null);
    Tok = tok;
    Name = label;
  }
}