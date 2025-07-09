using System.Collections.Concurrent;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class NodeTests {

  class ConcreteNode : NodeWithOrigin {
    public ConcreteNode(IOrigin origin, IEnumerable<INode>? children = null) : base(origin) {
      Children = children ?? [];
    }

    public override IEnumerable<INode> Children { get; }
    public override IEnumerable<INode> PreResolveChildren => Children;
  }

  private static SourceOrigin CreateRange(Uri uri, int startLine, int startColumn, int endLine, int endColumn) {
    return new SourceOrigin(new Token(startLine + 1, startColumn + 1) { Uri = uri }, new Token(endLine + 1, endColumn + 1) { Uri = uri });
  }

  [Fact]
  public void FindNodeWithTokenLessIntermediate() {
    var uri = new Uri(Directory.GetCurrentDirectory());
    var child = new ConcreteNode(CreateRange(uri, 0, 1, 0, 2));
    var parent = new ConcreteNode(SourceOrigin.NoToken, (IEnumerable<INode>)new INode[] { child });
    var grandParent = new ConcreteNode(CreateRange(uri, 0, 0, 0, 3), (IEnumerable<INode>)new INode[] { parent });

    var shouldBeChild = grandParent.FindNode<INode>(uri, new DafnyPosition(0, 1));
    Assert.Equal(child, shouldBeChild);
  }

  [Fact]
  public void SkipTokenlessLeaf() {
    var uri = new Uri(Directory.GetCurrentDirectory());
    var child1 = new ConcreteNode(SourceOrigin.NoToken);
    var child2 = new ConcreteNode(CreateRange(uri, 0, 1, 0, 2));

    var parent = new ConcreteNode(CreateRange(uri, 0, 0, 0, 3), (IEnumerable<INode>)new[] { child1, child2 });

    var shouldBeChild = parent.FindNode<INode>(uri, new DafnyPosition(0, 1));
    Assert.Equal(child2, shouldBeChild);
  }
}