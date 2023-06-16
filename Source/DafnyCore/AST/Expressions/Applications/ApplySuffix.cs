using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// An ApplySuffix desugars into either an ApplyExpr or a FunctionCallExpr
/// </summary>
public class ApplySuffix : SuffixExpr, ICloneable<ApplySuffix>, ICanFormat {
  public readonly IToken/*?*/ AtTok;
  public readonly IToken CloseParen;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;

  public override IEnumerable<Node> Children => ResolvedExpression == null
    ? base.Children.Concat(Bindings == null ? new List<Node>() : Args ?? Enumerable.Empty<Node>()) : new[] { ResolvedExpression };
  public override IEnumerable<Node> PreResolveChildren => new List<Node> { Lhs, Bindings };

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Args != null);
  }

  public ApplySuffix Clone(Cloner cloner) {
    return new ApplySuffix(cloner, this);
  }

  public ApplySuffix(Cloner cloner, ApplySuffix original) :
    base(cloner, original) {
    AtTok = original.AtTok == null ? null : cloner.Tok(original.AtTok);
    CloseParen = cloner.Tok(original.CloseParen);
    FormatTokens = original.FormatTokens;
    Bindings = new ActualBindings(cloner, original.Bindings);
  }

  public ApplySuffix(IToken tok, IToken/*?*/ atLabel, Expression lhs, List<ActualBinding> args, IToken closeParen)
    : base(tok, lhs) {
    Contract.Requires(tok != null);
    Contract.Requires(lhs != null);
    Contract.Requires(cce.NonNullElements(args));
    AtTok = atLabel;
    CloseParen = closeParen;
    Bindings = new ActualBindings(args);
    if (closeParen != null) {
      FormatTokens = new[] { closeParen };
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Lhs;
      if (Bindings.ArgumentBindings != null) {
        foreach (var binding in Bindings.ArgumentBindings) {
          yield return binding.Actual;
        }
      }
    }
  }

  /// <summary>
  /// Create an ApplySuffix expression using the most basic pieces: a target name and a list of expressions.
  /// </summary>
  /// <param name="tok">The location to associate with the new ApplySuffix expression.</param>
  /// <param name="name">The name of the target function or method.</param>
  /// <param name="args">The arguments to apply the function or method to.</param>
  /// <returns></returns>
  public static Expression MakeRawApplySuffix(IToken tok, string name, List<Expression> args) {
    var nameExpr = new NameSegment(tok, name, null);
    var argBindings = args.ConvertAll(arg => new ActualBinding(null, arg));
    return new ApplySuffix(tok, null, nameExpr, argBindings, tok);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var reindent = formatter.ReduceBlockiness ? indentBefore
      : formatter.GetNewTokenVisualIndent(StartToken, indentBefore);
    return formatter.SetIndentParensExpression(reindent, OwnedTokens);
  }
}