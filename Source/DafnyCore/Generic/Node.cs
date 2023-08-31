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
  public IToken StartToken => RangeToken.StartToken;
  public IToken EndToken => RangeToken.EndToken;
  IEnumerable<IToken> OwnedTokens { get; }
  RangeToken RangeToken { get; }
  IToken Tok { get; }
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

  protected IReadOnlyList<IToken> OwnedTokensCache;

  public IToken StartToken => RangeToken?.StartToken;

  public IToken EndToken => RangeToken?.EndToken;
  public abstract IToken Tok { get; }

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

  /// <summary>
  /// A token is owned by a node if it was used to parse this node,
  /// but is not owned by any of this Node's children
  /// </summary>
  public IEnumerable<IToken> OwnedTokens {
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

      var result = new List<IToken>();
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

  public abstract RangeToken RangeToken { get; set; }

  // <summary>
  // Returns all assumptions contained in this node or its descendants.
  // For each one, the decl field will be set to the closest containing declaration.
  // Likewise, the decl parameter to this method must be the closest declaration
  // containing this node, or null if it is not contained in any.
  // </summary>
  public virtual IEnumerable<Assumption> Assumptions(Declaration decl) {
    return Enumerable.Empty<Assumption>();
  }

  public ISet<INode> Visit(Func<INode, bool> beforeChildren = null, Action<INode> afterChildren = null) {
    beforeChildren ??= node => true;
    afterChildren ??= node => { };

    var visited = new HashSet<INode>();
    var toVisit = new LinkedList<INode>();
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

  // Docstring from start token is extracted only if using "/** ... */" syntax, and only the last one is considered
  protected string GetTriviaContainingDocstringFromStartTokenOrNull() {
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
}

public abstract class TokenNode : Node {
  // Contains tokens that did not make it in the AST but are part of the expression,
  // Enables ranges to be correct.
  // TODO: Re-add format tokens where needed until we put all the formatting to replace the tok of every expression
  internal IToken[] FormatTokens = null;

  protected RangeToken rangeToken = null;

  public IToken tok = Token.NoToken;

  [DebuggerBrowsable(DebuggerBrowsableState.Never)]
  public override IToken Tok {
    get => tok;
  }

  public override RangeToken RangeToken {
    get {
      if (rangeToken == null) {

        var startTok = tok;
        var endTok = tok;

        void UpdateStartEndToken(IToken token1) {
          if (token1.Filepath != tok.Filepath) {
            return;
          }

          if (token1.pos < startTok.pos) {
            startTok = token1;
          }

          if (token1.pos + token1.val.Length > endTok.pos + endTok.val.Length) {
            endTok = token1;
          }
        }

        void UpdateStartEndTokRecursive(INode node) {
          if (node is null) {
            return;
          }

          if (node.RangeToken.Filepath != tok.Filepath || node is Expression { IsImplicit: true } ||
              node is DefaultValueExpression) {
            // Ignore any auto-generated expressions.
          } else {
            UpdateStartEndToken(node.StartToken);
            UpdateStartEndToken(node.EndToken);
          }
        }

        PreResolveChildren.ForEach(UpdateStartEndTokRecursive);

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
