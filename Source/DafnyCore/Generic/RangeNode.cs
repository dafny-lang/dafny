namespace Microsoft.Dafny;

public abstract class RangeNode : Node {
  private IOrigin rangeToken; // TODO merge into Node when TokenNode is gone.

  public override IOrigin Tok => StartToken; // TODO remove

  public IOrigin tok => Tok; // TODO remove

  // TODO rename to Range in separate PR
  public override IOrigin RangeOrigin {
    set => rangeToken = value;
  } // TODO remove setter when TokenNode is gone.

  public override IOrigin Origin => rangeToken;

  protected RangeNode(Cloner cloner, RangeNode original) {
    RangeOrigin = cloner.Origin(original.rangeToken);
  }

  protected RangeNode(IOrigin rangeOrigin) {
    RangeOrigin = rangeOrigin;
  }
}