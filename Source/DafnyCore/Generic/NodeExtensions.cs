using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection.Metadata.Ecma335;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

public interface IHasDocstring {
  /// <summary>
  /// Unfiltered version that only returns the trivia containing the docstring
  /// </summary>
  public string GetTriviaContainingDocstring();
}

public static class NodeExtensions {



  public static IOrigin OriginWithEntireRange(this INode node) => new WithRange(node.Origin, node.EntireRange);

  /// <summary>
  /// // Applies plugin-defined docstring filters
  /// </summary>
  public static string GetDocstring(this IHasDocstring node, DafnyOptions options) {
    var plugins = options.Plugins;
    string trivia = node.GetTriviaContainingDocstring();
    if (string.IsNullOrEmpty(trivia)) {
      return null;
    }

    var rawDocstring = ExtractDocstring(trivia);
    foreach (var plugin in plugins) {
      foreach (var docstringRewriter in plugin.GetDocstringRewriters(options)) {
        rawDocstring = docstringRewriter.RewriteDocstring(rawDocstring) ?? rawDocstring;
      }
    }

    return rawDocstring;
  }

  private static string ExtractDocstring(string trivia) {
    var extraction = new Regex(
      $@"(?<multiline>(?<indentation>[ \t]*)/\*(?<multilinecontent>{TriviaFormatterHelper.MultilineCommentContent})\*/)" +
      $@"|(?<singleline>// ?(?<singlelinecontent>[^\r\n]*?)[ \t]*(?:{TriviaFormatterHelper.AnyNewline}|$))");
    var rawDocstring = new List<string>() { };
    var matches = extraction.Matches(trivia);
    for (var i = 0; i < matches.Count; i++) {
      var match = matches[i];
      if (match.Groups["multiline"].Success) {
        // For each line except the first,
        // we need to remove the indentation on every line.
        // The length of removed indentation is maximum the space before the first "/*" + 3 characters
        // Additionally, if there is a "* " or a " *" or a "  * ", we remove it as well
        // provided it always started with a star.
        var indentation = match.Groups["indentation"].Value;
        var multilineContent = match.Groups["multilinecontent"].Value;
        var newlineRegex = new Regex(TriviaFormatterHelper.AnyNewline);
        var contentLines = newlineRegex.Split(multilineContent);
        var starRegex = new Regex(@"^[ \t]*\*\ ?(?<remaining>.*)$");
        var wasNeverInterrupted = true;
        var localDocstring = "";
        for (var j = 0; j < contentLines.Length; j++) {
          if (j != 0) {
            localDocstring += "\n";
          }
          var contentLine = contentLines[j];
          var lineMatch = starRegex.Match(contentLine);
          if (lineMatch.Success && wasNeverInterrupted) {
            localDocstring += lineMatch.Groups["remaining"].Value;
          } else {
            if (j == 0) {
              localDocstring += contentLine.TrimStart();
            } else {
              wasNeverInterrupted = false;
              if (contentLine.StartsWith(indentation)) {
                var trimmedIndentation =
                  contentLine.Substring(0, Math.Min(indentation.Length + 3, contentLine.Length)).TrimStart();
                var remaining = (contentLine.Length >= indentation.Length + 3
                  ? contentLine.Substring(indentation.Length + 3)
                  : "");
                localDocstring += trimmedIndentation + remaining;
              } else {
                localDocstring += contentLine.Trim();
              }
            }
          }
        }

        localDocstring = localDocstring.Trim();
        rawDocstring.Add(localDocstring);
      } else if (match.Groups["singleline"].Success) {
        rawDocstring.Add(match.Groups["singlelinecontent"].Value);
      }
    }

    return string.Join("\n", rawDocstring);
  }

  public static IEnumerable<INode> Descendants(this INode node) {
    return node.Children.Concat(node.Children.SelectMany(n => n.Descendants()));
  }

  public static T FindNode<T>(this INode root, Uri uri, DafnyPosition position) {
    return (T)root.FindNodeChain(uri, position, null, node => node is T)?.Data;
  }

  public static INode FindNode(this INode node, Uri uri, DafnyPosition position, Func<INode, bool> predicate) {
    return node.FindNodeChain(uri, position, null, predicate)?.Data;
  }

  public static IEnumerable<INode> FindNodesInUris(this INode node, Uri uri) {
    return node.FindNodeChainsInUri(uri, null).Select(c => c.Data);
  }

  public static IEnumerable<LList<INode>> FindNodeChainsInUri(this INode node, Uri uri, LList<INode> parent) {
    if (node.Origin.Uri != null) {
      if (node.Origin.Uri == uri) {
        return new[] { new LList<INode>(node, parent) };
      }

      return new LList<INode>[] { };
    }

    var newParent = new LList<INode>(node, parent);
    return node.Children.SelectMany(child => child.FindNodeChainsInUri(uri, newParent));
  }

  private static LList<INode> FindNodeChain(this INode node, Uri uri, DafnyPosition position, LList<INode> parent,
    Func<INode, bool> predicate) {
    if (node.Origin.Uri != null) {
      if (node.Origin.Uri == uri) {
        return node.FindNodeChain(position, parent, predicate);
      }

      if (node.SingleFileToken) {
        return null;
      }
    }

    var newParent = new LList<INode>(node, parent);
    foreach (var child in node.Children) {
      var result = child.FindNodeChain(uri, position, newParent, predicate);
      if (result != null) {
        return result;
      }
    }

    return null;
  }

  public static LList<INode> FindNodeChain(this INode node, DafnyPosition position, Func<INode, bool> predicate) {
    return FindNodeChain(node, position, new LList<INode>(node, null), predicate);
  }

  private static LList<INode> FindNodeChain(this INode node, DafnyPosition position, LList<INode> parent,
    Func<INode, bool> predicate) {
    if (node.Origin is AutoGeneratedOrigin) {
      return null;
    }

    // Example of a fillerNode is the default class, although we could give it the same origin as the module it is in.
    var fillerNode = !ReferenceEquals(node.Origin, Token.NoToken);
    if (fillerNode && !node.ToDafnyRange().Contains(position)) {
      return null;
    }

    var newParent = new LList<INode>(node, parent);
    foreach (var child in node.Children) {
      var result = child.FindNodeChain(position, newParent, predicate);
      if (result != null) {
        return result;
      }
    }

    if (ReferenceEquals(node.Origin, Token.NoToken) || !predicate(node)) {
      return null;
    }

    return new LList<INode>(node, parent);
  }
}