namespace Microsoft.Dafny;

public abstract class RangeNode : Node { // TODO merge into Node when TokenNode is gone.

  public override IOrigin Tok => StartToken; // TODO rename to ReportingToken in separate PR

  public IOrigin tok => Tok; // TODO replace with Tok in separate PR

  // TODO rename to Range in separate PR
  public override IOrigin RangeToken { get; set; } // TODO remove setter when TokenNode is gone.

  protected RangeNode(Cloner cloner, RangeNode original) {
    RangeToken = cloner.Tok(original.RangeToken);
  }

  protected RangeNode(IOrigin rangeToken) {
    RangeToken = rangeToken;
  }
}