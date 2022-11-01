using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public interface INode {

  /// <summary>
  /// These children should be such that they contain information produced by resolution such as inferred types
  /// and resolved references. However, they should not be so transformed that source location from the initial
  /// program is lost. As an example, the pattern matching compilation may deduplicate nodes from the original AST,
  /// losing source location information, so those transformed nodes should not be returned by this property.
  /// </summary>
  IEnumerable<INode> Children { get; }

  public ISet<INode> Visit(Func<INode, bool> beforeChildren = null, Action<INode> afterChildren = null) {
    beforeChildren ??= node => true;
    afterChildren ??= node => { };

    var visited = new HashSet<INode>();
    var toVisit = new Stack<INode>();
    toVisit.Push(this);
    while (toVisit.Any()) {
      var current = toVisit.Pop();
      if (!visited.Add(current)) {
        continue;
      }

      if (!beforeChildren(current)) {
        continue;
      }

      foreach (var child in current.Children) {
        if (child == null) {
          throw new InvalidOperationException($"Object of type {current.GetType()} has null child");
        }
        toVisit.Push(child);
      }

      afterChildren(current);
    }

    return visited;
  }
}