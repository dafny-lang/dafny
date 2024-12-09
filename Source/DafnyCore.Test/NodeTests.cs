using System.Collections.Concurrent;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NodeTests {

  class ConcreteNode : Node {
    public ConcreteNode(RangeToken rangeToken, IEnumerable<INode>? children = null) {
      RangeToken = rangeToken;
      Children = children ?? Enumerable.Empty<INode>();
    }

    public override RangeToken RangeToken { get; set; }
    public override IToken Tok => RangeToken.StartToken;
    public override IEnumerable<INode> Children { get; }
    public override IEnumerable<INode> PreResolveChildren => Children;
  }

  private static RangeToken CreateRange(Uri uri, int startLine, int startColumn, int endLine, int endColumn) {
    return new RangeToken(new Token(startLine + 1, startColumn + 1) { Uri = uri }, new Token(endLine + 1, endColumn + 1) { Uri = uri });
  }

  [Fact]
  public void FindNodeWithTokenLessIntermediate() {
    var uri = new Uri(Directory.GetCurrentDirectory());
    var child = new ConcreteNode(CreateRange(uri, 0, 1, 0, 2));
    var parent = new ConcreteNode(RangeToken.NoToken, (IEnumerable<INode>)new INode[] { child });
    var grandParent = new ConcreteNode(CreateRange(uri, 0, 0, 0, 3), (IEnumerable<INode>)new INode[] { parent });

    var shouldBeChild = grandParent.FindNode<INode>(uri, new DafnyPosition(0, 1));
    Assert.Equal(child, shouldBeChild);
  }

  [Fact]
  public void SkipTokenlessLeaf() {
    var uri = new Uri(Directory.GetCurrentDirectory());
    var child1 = new ConcreteNode(RangeToken.NoToken);
    var child2 = new ConcreteNode(CreateRange(uri, 0, 1, 0, 2));

    var parent = new ConcreteNode(CreateRange(uri, 0, 0, 0, 3), (IEnumerable<INode>)new[] { child1, child2 });

    var shouldBeChild = parent.FindNode<INode>(uri, new DafnyPosition(0, 1));
    Assert.Equal(child2, shouldBeChild);
  }
}