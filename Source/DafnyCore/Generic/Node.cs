using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Dafny.Auditor;
using Action = System.Action;

namespace Microsoft.Dafny;

public interface INode {
  bool SingleFileToken { get; }
  public Token StartToken => Origin.StartToken;
  public Token EndToken => Origin.EndToken;
  IEnumerable<IOrigin> OwnedTokens { get; }
  IOrigin Origin { get; }
  IOrigin Tok { get; }
  IEnumerable<INode> Children { get; }
  IEnumerable<INode> PreResolveChildren { get; }
}

public interface ICanFormat : INode {
  /// Sets the indentation of individual tokens owned by this node, given
  /// the new indentation set by the tokens preceding this node
  /// Returns if further traverse needs to occur (true) or if it already happened (false)
  bool SetIndent(int indentBefore, TokenNewIndentCollector formatter);
}


public abstract class Node : INode {
  private static readonly Regex StartDocstringExtractor =
    new Regex($@"/\*\*(?<multilinecontent>{TriviaFormatterHelper.MultilineCommentContent})\*/");

  protected IReadOnlyList<IOrigin> OwnedTokensCache;

  public virtual bool SingleFileToken => true;
  public Token StartToken => Origin?.StartToken;

  public Token EndToken => Origin?.EndToken;
  public abstract IOrigin Tok { get; }

  /// <summary>
  /// These children should be such that they contain information produced by resolution such as inferred types
  /// and resolved references. However, they should not be so transformed that source location from the initial
  /// program is lost. As an example, the pattern matching compilation may deduplicate nodes from the original AST,
  /// losing source location information, so those transformed nodes should not be returned by this property.
  /// </summary>
  public abstract IEnumerable<INode> Children { get; }

  /// <summary>
  /// These children should match what was parsed before the resolution phase.
  /// That way, gathering all OwnedTokens of all recursive ConcreteChildren should result in a comprehensive
  /// coverage of the original program
  /// </summary>
  public abstract IEnumerable<INode> PreResolveChildren { get; }

  public IEnumerable<Token> CoveredTokens {
    get {
      var token = StartToken;
      if (token == Token.NoToken) {
        yield break;
      }
      while (token.Prev != EndToken) {
        yield return token;
        token = token.Next;
      }
    }
  }

  /// <summary>
  /// A token is owned by a node if it was used to parse this node,
  /// but is not owned by any of this Node's children
  /// </summary>
  public IEnumerable<IOrigin> OwnedTokens {
    get {
      if (OwnedTokensCache != null) {
        return OwnedTokensCache;
      }

      var childrenFiltered = GetConcreteChildren(this).ToList();

      // If we parse a resolved document, some children sometimes have the same token because they are auto-generated
      var startToEndTokenNotOwned = childrenFiltered.
        // Because RangeToken.EndToken is inclusive, a token with an empty range has an EndToken that occurs before the StartToken
        // We need to filter these out to prevent an infinite loop
        Where(c => c.StartToken.pos <= c.EndToken.pos).
        GroupBy(child => child.StartToken.pos).
        ToDictionary(g => g.Key, g => g.MaxBy(child => child.EndToken.pos).EndToken
      );

      var result = new List<IOrigin>();
      if (StartToken == null) {
        Contract.Assume(EndToken == null);
      } else {
        Contract.Assume(EndToken != null);
        var tmpToken = StartToken;
        while (tmpToken != null && tmpToken != EndToken.Next) {
          if (startToEndTokenNotOwned.TryGetValue(tmpToken.pos, out var endNotOwnedToken)) {
            tmpToken = endNotOwnedToken;
          } else if (tmpToken.Uri != null) {
            result.Add(tmpToken);
          }

          tmpToken = tmpToken.Next;
        }
      }


      OwnedTokensCache = result;

      return OwnedTokensCache;
    }
  }

  /// <summary>
  // Nodes like DefaultClassDecl have children but no OwnedTokens as they are not "physical"
  // Therefore, we have to find all the concrete children by unwrapping such nodes. 
  /// </summary>
  private static IEnumerable<INode> GetConcreteChildren(INode node) {
    foreach (var child in node.PreResolveChildren) {
      if (child.StartToken != null && child.EndToken != null && child.StartToken.line != 0) {
        yield return child;
      } else {
        foreach (var subNode in GetConcreteChildren(child)) {
          yield return subNode;
        }
      }
    }
  }

  public abstract IOrigin Origin { get; set; }

  // <summary>
  // Returns all assumptions contained in this node or its descendants.
  // For each one, the decl field will be set to the closest containing declaration.
  // Likewise, the decl parameter to this method must be the closest declaration
  // containing this node, or null if it is not contained in any.
  // </summary>
  public virtual IEnumerable<Assumption> Assumptions(Declaration decl) {
    return Enumerable.Empty<Assumption>();
  }

  public ISet<INode> Visit(Func<INode, bool> beforeChildren = null, Action<INode> afterChildren = null, Action<Exception> reportError = null) {
    reportError ??= _ => { };
    beforeChildren ??= node => true;

    var visited = new HashSet<INode>();
    var toVisit = new LinkedList<object>();
    toVisit.AddFirst(this);
    while (toVisit.Any()) {
      var current = toVisit.First();
      toVisit.RemoveFirst();
      if (current is INode currentNode) {
        if (!visited.Add(currentNode)) {
          continue;
        }

        if (!beforeChildren(currentNode)) {
          continue;
        }

        if (afterChildren != null) {
          void AfterNodeChildren() => afterChildren(currentNode);
          toVisit.AddFirst((Action)AfterNodeChildren);
        }
        var nodeAfterChildren = toVisit.First;
        foreach (var child in currentNode.Children) {
          if (child == null) {
            reportError(new InvalidOperationException($"Object of type {current.GetType()} has null child"));
            continue;
          }

          if (nodeAfterChildren == null) {
            toVisit.AddLast(child);
          } else {
            // Depth-first, but with children in unreversed order
            toVisit.AddBefore(nodeAfterChildren, child);
          }
        }
      } else {
        var currentAction = (Action)current;
        currentAction();
      }
    }

    return visited;
  }

  // Docstring from start token is extracted only if using "/** ... */" syntax, and only the last one is considered
  protected bool GetStartTriviaDocstring(out string trivia) {
    var matches = StartDocstringExtractor.Matches(StartToken.LeadingTrivia);
    trivia = null;
    if (matches.Count > 0) {
      trivia = matches[^1].Value;
    } else if (StartToken.Prev is { val: "|" or "{" }) {
      matches = StartDocstringExtractor.Matches(StartToken.Prev.TrailingTrivia);
      if (matches.Count > 0) {
        trivia = matches[^1].Value;
      }
    }
    return trivia is not ("" or null);
  }
}