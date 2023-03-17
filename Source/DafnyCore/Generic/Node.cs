using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;


public interface INode {
  RangeToken RangeToken { get; }

  IToken Tok { get; }
}

public interface ICanFormat : INode {
  /// Sets the indentation of individual tokens owned by this node, given
  /// the new indentation set by the tokens preceding this node
  /// Returns if further traverse needs to occur (true) or if it already happened (false)
  bool SetIndent(int indentBefore, TokenNewIndentCollector formatter);
}

// A node that can have a docstring attached to it
public interface IHasDocstring : INode {
  string GetDocstring(DafnyOptions options);
}

public abstract class Node : INode {

  public abstract IToken Tok { get; }

  /// <summary>
  /// These children should be such that they contain information produced by resolution such as inferred types
  /// and resolved references. However, they should not be so transformed that source location from the initial
  /// program is lost. As an example, the pattern matching compilation may deduplicate nodes from the original AST,
  /// losing source location information, so those transformed nodes should not be returned by this property.
  /// </summary>
  public abstract IEnumerable<Node> Children { get; }

  /// <summary>
  /// These children should match what was parsed before the resolution phase.
  /// That way, gathering all OwnedTokens of all recursive ConcreteChildren should result in a comprehensive
  /// coverage of the original program
  /// </summary>
  public abstract IEnumerable<Node> PreResolveChildren { get; }

  // Nodes like DefaultClassDecl have children but no OwnedTokens as they are not "physical"
  // Therefore, we have to find all the concrete children by unwrapping such nodes.
  private IEnumerable<Node> GetConcreteChildren() {
    foreach (var child in PreResolveChildren) {
      if (child.StartToken != null && child.EndToken != null && child.StartToken.line != 0) {
        yield return child;
      } else {
        foreach (var subNode in child.GetConcreteChildren()) {
          yield return subNode;
        }
      }
    }
  }


  public IEnumerable<Node> Descendants() {
    return Children.Concat(Children.SelectMany(n => n.Descendants()));
  }

  public virtual IEnumerable<AssumptionDescription> Assumptions() {
    return Enumerable.Empty<AssumptionDescription>();
  }

  public ISet<Node> Visit(Func<Node, bool> beforeChildren = null, Action<Node> afterChildren = null) {
    beforeChildren ??= node => true;
    afterChildren ??= node => { };

    var visited = new HashSet<Node>();
    var toVisit = new LinkedList<Node>();
    toVisit.AddFirst(this);
    while (toVisit.Any()) {
      var current = toVisit.First();
      toVisit.RemoveFirst();
      if (!visited.Add(current)) {
        continue;
      }

      if (!beforeChildren(current)) {
        continue;
      }

      var nodeAfterChildren = toVisit.First;
      foreach (var child in current.Children) {
        if (child == null) {
          throw new InvalidOperationException($"Object of type {current.GetType()} has null child");
        }

        if (nodeAfterChildren == null) {
          toVisit.AddLast(child);
        } else {
          toVisit.AddBefore(nodeAfterChildren, child);
        }
      }

      afterChildren(current);
    }

    return visited;
  }


  public IToken StartToken => RangeToken?.StartToken;

  public IToken EndToken => RangeToken?.EndToken;

  protected IReadOnlyList<IToken> OwnedTokensCache;

  private static readonly Regex StartDocstringExtractor =
    new Regex($@"/\*\*(?<multilinecontent>{TriviaFormatterHelper.MultilineCommentContent})\*/");

  /// <summary>
  /// A token is owned by a node if it was used to parse this node,
  /// but is not owned by any of this Node's children
  /// </summary>
  public IEnumerable<IToken> OwnedTokens {
    get {
      if (OwnedTokensCache != null) {
        return OwnedTokensCache;
      }

      var childrenFiltered = GetConcreteChildren().ToList();

      Dictionary<int, IToken> startToEndTokenNotOwned;
      try {
        startToEndTokenNotOwned =
          childrenFiltered
            .ToDictionary(child => child.StartToken.pos, child => child.EndToken!);
      } catch (ArgumentException) {
        // If we parse a resolved document, some children sometimes have the same token because they are auto-generated
        startToEndTokenNotOwned = new();
        foreach (var child in childrenFiltered) {
          if (startToEndTokenNotOwned.ContainsKey(child.StartToken.pos)) {
            var previousEnd = startToEndTokenNotOwned[child.StartToken.pos];
            if (child.EndToken.pos > previousEnd.pos) {
              startToEndTokenNotOwned[child.StartToken.pos] = child.EndToken;
            }
          } else {
            startToEndTokenNotOwned[child.StartToken.pos] = child.EndToken;
          }
        }
      }

      var result = new List<IToken>();
      if (StartToken == null) {
        Contract.Assume(EndToken == null);
      } else {
        Contract.Assume(EndToken != null);
        var tmpToken = StartToken;
        while (tmpToken != null && tmpToken != EndToken.Next) {
          if (startToEndTokenNotOwned.TryGetValue(tmpToken.pos, out var endNotOwnedToken)) {
            tmpToken = endNotOwnedToken;
          } else if (tmpToken.filename != null) {
            result.Add(tmpToken);
          }

          tmpToken = tmpToken.Next;
        }
      }


      OwnedTokensCache = result;

      return OwnedTokensCache;
    }
  }

  public abstract RangeToken RangeToken { get; set; }

  // Docstring from start token is extracted only if using "/** ... */" syntax, and only the last one is considered
  protected string GetTriviaContainingDocstringFromStartTokeOrNull() {
    var matches = StartDocstringExtractor.Matches(StartToken.LeadingTrivia);
    if (matches.Count > 0) {
      return matches[^1].Value;
    }

    if (StartToken.Prev.val is "|" or "{") {
      matches = StartDocstringExtractor.Matches(StartToken.Prev.TrailingTrivia);
      if (matches.Count > 0) {
        return matches[^1].Value;
      }
    }
    return null;
  }

  // Applies plugin-defined docstring filters
  public string GetDocstring(DafnyOptions options) {
    var plugins = options.Plugins;
    string trivia = GetTriviaContainingDocstring();
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

  private string ExtractDocstring(string trivia) {
    var extraction = new Regex(
      $@"(?<multiline>(?<indentation>[ \t]*)/\*(?<multilinecontent>{TriviaFormatterHelper.MultilineCommentContent})\*/)" +
      $@"|(?<singleline>// ?(?<singlelinecontent>[^\r\n]*?)[ \t]*(?:{TriviaFormatterHelper.AnyNewline}|$))");
    var rawDocstring = new List<string>() { };
    var matches = extraction.Matches(trivia);
    for (var i = 0; i < matches.Count; i++) {
      var match = matches[i];
      if (match.Groups["multiline"].Success) {
        // For each line except the first,
        // we need to remove the indentation up to the first "/" of the comment
        // Additionally, if there is a "* " or a " *" or a "  * ", we remove it as well
        // provided it always started with a star.
        //var startIndex = match.Groups["multiline"].Index;
        //var indentation = trivia.
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

  // Unfiltered version that only returns the trivia containing the docstring
  protected virtual string GetTriviaContainingDocstring() {
    return null;
  }
}

public abstract class TokenNode : Node {

  public IToken tok = Token.NoToken;
  [DebuggerBrowsable(DebuggerBrowsableState.Never)]
  public override IToken Tok {
    get => tok;
  }

  protected RangeToken rangeToken = null;

  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal IToken[] FormatTokens = null;

  public override RangeToken RangeToken {
    get {
      if (rangeToken == null) {

        var startTok = tok;
        var endTok = tok;

        void UpdateStartEndToken(IToken token1) {
          if (token1.Filename != tok.Filename) {
            return;
          }

          if (token1.pos < startTok.pos) {
            startTok = token1;
          }

          if (token1.pos + token1.val.Length > endTok.pos + endTok.val.Length) {
            endTok = token1;
          }
        }

        void UpdateStartEndTokRecursive(Node node) {
          if (node is null) {
            return;
          }

          if (node.RangeToken.Filename != tok.Filename || node is Expression { IsImplicit: true } ||
              node is DefaultValueExpression) {
            // Ignore any auto-generated expressions.
          } else {
            UpdateStartEndToken(node.StartToken);
            UpdateStartEndToken(node.EndToken);
          }
        }

        Children.Iter(UpdateStartEndTokRecursive);

        if (FormatTokens != null) {
          foreach (var token in FormatTokens) {
            UpdateStartEndToken(token);
          }
        }

        rangeToken = new RangeToken(startTok, endTok);
      }

      return rangeToken;
    }
    set => rangeToken = value;
  }
}

public abstract class RangeNode : Node { // TODO merge into Node when TokenNode is gone.
  public override IToken Tok => StartToken; // TODO rename to ReportingToken in separate PR

  public IToken tok => Tok; // TODO replace with Tok in separate PR

  // TODO rename to Range in separate PR
  public override RangeToken RangeToken { get; set; } // TODO remove setter when TokenNode is gone.

  protected RangeNode(Cloner cloner, RangeNode original) {
    RangeToken = cloner.Tok(original.RangeToken);
  }

  protected RangeNode(RangeToken rangeToken) {
    RangeToken = rangeToken;
  }
}