namespace Microsoft.Dafny;

public abstract class RangeNode : Node { // TODO merge into Node when TokenNode is gone.

  public override IOrigin Tok => Origin;

  public override IOrigin Origin { get; set; } // TODO remove setter when TokenNode is gone.

  protected RangeNode(Cloner cloner, RangeNode original) {
    Origin = cloner.Origin(original.Origin);
  }

  protected RangeNode(IOrigin rangeOrigin) {
    Origin = rangeOrigin;
  }
}