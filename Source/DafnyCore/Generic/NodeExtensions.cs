using System;
using System.Linq;

namespace Microsoft.Dafny;

public static class NodeExtensions {

  public static INode FindNode(this INode node, Uri uri, DafnyPosition position) {
    if (node.Tok.Uri != null) {
      if (node.Tok.Uri == uri) {
        return node.FindNode(position);
      }

      return null;
    }

    foreach (var child in node.Children) {
      var result = child.FindNode(uri, position);
      if (result != null) {
        return result;
      }
    }

    return null;
  }
  private static INode FindNode(this INode node, DafnyPosition position) {
    if (!node.RangeToken.ToDafnyRange().Contains(position)) {
      return null;
    }

    foreach (var child in node.Children) {
      var result = child.FindNode(position);
      if (result != null) {
        return result;
      }
    }

    return node;
  }
}