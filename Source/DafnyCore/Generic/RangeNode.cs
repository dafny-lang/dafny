using Newtonsoft.Json;

namespace Microsoft.Dafny;

public abstract class RangeNode : Node {
  private IOrigin origin; // TODO merge into Node when TokenNode is gone.

  public override IOrigin Origin => origin;

  protected RangeNode(Cloner cloner, RangeNode original) {
    origin = cloner.Origin(original.Origin);
  }

  [ParseConstructor]
  protected RangeNode(IOrigin origin) {
    this.origin = origin;
  }

  public void SetOrigin(IOrigin newOrigin) {
    origin = newOrigin;
  }
}