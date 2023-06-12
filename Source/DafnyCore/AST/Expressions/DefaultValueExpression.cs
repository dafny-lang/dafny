using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// When an actual parameter is omitted for a formal with a default value, the positional resolved
/// version of the actual parameter will have a DefaultValueExpression value. This has three
/// advantages:
/// * It allows the entire module to be resolved before any substitutions take place.
/// * It gives a good place to check for default-value expressions that would give rise to an
///   infinite expansion.
/// * It preserves the pre-substitution form, which gives compilers a chance to avoid re-evaluation
///   of actual parameters used in other default-valued expressions.
///
/// Note. Since DefaultValueExpression is a wrapper around another expression and can in several
/// places be expanded according to its ResolvedExpression, it is convenient to make DefaultValueExpression
/// inherit from ConcreteSyntaxExpression. However, there are some places in the code where
/// one then needs to pay attention to DefaultValueExpression's. Such places would be more
/// conspicuous if DefaultValueExpression were not an Expression at all. At the time of this
/// writing, a change to a separate type has shown to be more hassle than the need for special
/// attention to DefaultValueExpression's in some places.
/// </summary>
public class DefaultValueExpression : ConcreteSyntaxExpression, ICloneable<DefaultValueExpression> {
  public readonly Formal Formal;
  public readonly Expression Receiver;
  public readonly Dictionary<IVariable, Expression> SubstMap;
  public readonly Dictionary<TypeParameter, Type> TypeMap;

  public DefaultValueExpression(IToken tok, Formal formal,
    Expression/*?*/ receiver, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(formal != null);
    Contract.Requires(formal.DefaultValue != null);
    Contract.Requires(substMap != null);
    Contract.Requires(typeMap != null);
    Formal = formal;
    Receiver = receiver;
    SubstMap = substMap;
    TypeMap = typeMap;
    Type = formal.Type.Subst(typeMap);
    RangeToken = new RangeToken(tok, tok);
  }

  public DefaultValueExpression(Cloner cloner, DefaultValueExpression original) : base(cloner, original) {
    if (!cloner.CloneResolvedFields) {
      throw new InvalidOperationException("DefaultValueExpression is created during resolution");
    }
    Formal = cloner.CloneFormal(original.Formal, true);
    Receiver = cloner.CloneExpr(original.Receiver);
    SubstMap = original.SubstMap;
    TypeMap = original.TypeMap;
  }

  public DefaultValueExpression Clone(Cloner cloner) {
    return new DefaultValueExpression(cloner, this);
  }
}