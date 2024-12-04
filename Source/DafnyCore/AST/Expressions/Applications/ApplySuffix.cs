using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// An ApplySuffix desugars into either an ApplyExpr or a FunctionCallExpr
/// </summary>
public class ApplySuffix : SuffixExpr, ICloneable<ApplySuffix>, ICanFormat {
  public readonly IOrigin/*?*/ AtTok;
  public readonly Token CloseParen;
  public readonly ActualBindings Bindings;
  public List<Expression> Args => Bindings.Arguments;
  [FilledInDuringResolution] public MethodCallInformation MethodCallInfo = null; // resolution will set to a non-null value if ApplySuffix makes a method call

  public override IEnumerable<INode> Children => ResolvedExpression == null
    ? base.Children.Concat(Bindings == null ? new List<Node>() : Args ?? Enumerable.Empty<Node>()) : new[] { ResolvedExpression };
  public override IEnumerable<INode> PreResolveChildren => new List<Node> { Lhs, Bindings };

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Args != null);
  }

  public ApplySuffix Clone(Cloner cloner) {
    return new ApplySuffix(cloner, this);
  }

  public ApplySuffix(Cloner cloner, ApplySuffix original) :
    base(cloner, original) {
    AtTok = original.AtTok == null ? null : cloner.Origin(original.AtTok);
    CloseParen = original.CloseParen;
    FormatTokens = original.FormatTokens;
    Bindings = new ActualBindings(cloner, original.Bindings);
  }

  public ApplySuffix(IOrigin tok, IOrigin/*?*/ atLabel, Expression lhs, List<ActualBinding> args, Token closeParen)
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
  public static Expression MakeRawApplySuffix(IOrigin tok, string name, List<Expression> args) {
    var nameExpr = new NameSegment(tok, name, null);
    var argBindings = args.ConvertAll(arg => new ActualBinding(null, arg));
    return new ApplySuffix(tok, null, nameExpr, argBindings, Token.NoToken);
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var reindent = formatter.ReduceBlockiness ? indentBefore
      : formatter.GetNewTokenVisualIndent(StartToken, indentBefore);
    return formatter.SetIndentParensExpression(reindent, OwnedTokens);
  }
}