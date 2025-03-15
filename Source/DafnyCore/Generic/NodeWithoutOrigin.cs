#nullable enable
namespace Microsoft.Dafny;

public abstract class NodeWithoutOrigin : Node {
  private IOrigin? origin;

  public override IOrigin Origin => origin ??= new SourceOrigin(EntireRange);

  public override TokenRange EntireRange => new(Token.NoToken, Token.NoToken);
}