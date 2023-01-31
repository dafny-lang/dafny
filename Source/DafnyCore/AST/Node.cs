using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public interface INode {
  RangeToken RangeToken { get; }
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

  /// <summary>
  /// A token is owned by a node if it was used to parse this node,
  /// but is not owned by any of this Node's children
  /// </summary>
  public IEnumerable<IToken> OwnedTokens {
    get {
      if (OwnedTokensCache != null) {
        return OwnedTokensCache;
      }

      var startToEndTokenNotOwned =
        Children.Where(child => child.StartToken != null && child.EndToken != null)
          .ToDictionary(child => child.StartToken!, child => child.EndToken!);

      var result = new List<IToken>();
      if (StartToken == null) {
        Contract.Assume(EndToken == null);
      } else {
        Contract.Assume(EndToken != null);
        var tmpToken = StartToken;
        while (tmpToken != null && tmpToken != EndToken.Next) {
          if (startToEndTokenNotOwned.TryGetValue(tmpToken, out var endNotOwnedToken)) {
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