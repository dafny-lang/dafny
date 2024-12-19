using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

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
public abstract class DefaultValueExpression : ConcreteSyntaxExpression {
  private readonly Formal formal;
  private readonly Expression receiver;
  private readonly Dictionary<IVariable, Expression> substMap;

  protected abstract Dictionary<TypeParameter, Type> GetTypeMap();

  public enum WorkProgress { BeingVisited, Done }

  protected DefaultValueExpression(IOrigin tok, Formal formal, Expression/*?*/ receiver, Dictionary<IVariable, Expression> substMap)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(formal != null);
    Contract.Requires(formal.DefaultValue != null);
    Contract.Requires(substMap != null);
    this.formal = formal;
    this.receiver = receiver;
    this.substMap = substMap;
  }

  protected DefaultValueExpression(Cloner cloner, DefaultValueExpression original) : base(cloner, original) {
    if (!cloner.CloneResolvedFields) {
      throw new InvalidOperationException("DefaultValueExpression is created during resolution");
    }
    formal = cloner.CloneFormal(original.formal, true);
    receiver = cloner.CloneExpr(original.receiver);
    substMap = original.substMap;
  }

  public void FillIn(ModuleResolver resolver, Dictionary<DefaultValueExpression, WorkProgress> visited) {
    if (visited.TryGetValue(this, out var p)) {
      if (p == WorkProgress.Done) {
        Contract.Assert(this.ResolvedExpression != null);
      } else {
        // there is a cycle
        resolver.reporter.Error(MessageSource.Resolver, this,
          "default-valued expressions are cyclicly dependent; this is not allowed, since it would cause infinite expansion");
        // nevertheless, to avoid any issues in the resolver, fill in the .ResolvedExpression field with something
        this.ResolvedExpression = Expression.CreateBoolLiteral(this.Tok, false);
      }
      return;
    }
    Contract.Assert(this.ResolvedExpression == null);

    visited.Add(this, WorkProgress.BeingVisited);
    var typeMap = GetTypeMap();
    var s = new DefaultValueSubstituter(resolver, visited, this.receiver, this.substMap, typeMap);
    this.ResolvedExpression = s.Substitute(this.formal.DefaultValue);
    visited[this] = WorkProgress.Done;
  }

  class DefaultValueSubstituter : Substituter {
    private readonly ModuleResolver resolver;
    private readonly Dictionary<DefaultValueExpression, DefaultValueExpression.WorkProgress> visited;
    public DefaultValueSubstituter(ModuleResolver resolver, Dictionary<DefaultValueExpression, DefaultValueExpression.WorkProgress> visited,
      Expression /*?*/ receiverReplacement, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
      : base(receiverReplacement, substMap, typeMap) {
      Contract.Requires(resolver != null);
      Contract.Requires(visited != null);
      this.resolver = resolver;
      this.visited = visited;
    }

    public override Expression Substitute(Expression expr) {
      if (expr is DefaultValueExpression dve) {
        dve.FillIn(resolver, visited);
        Contract.Assert(dve.ResolvedExpression != null); // postcondition of FillIn
      }
      return base.Substitute(expr);
    }
  }
}

public class DefaultValueExpressionType : DefaultValueExpression, ICloneable<DefaultValueExpressionType> {
  private readonly Dictionary<TypeParameter, Type> typeMap;

  public DefaultValueExpressionType(IOrigin tok, Formal formal,
    Expression/*?*/ receiver, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
    : base(tok, formal, receiver, substMap) {
    this.typeMap = typeMap;
  }

  public DefaultValueExpressionType(Cloner cloner, DefaultValueExpressionType original) : base(cloner, original) {
    typeMap = original.typeMap;
  }

  public DefaultValueExpressionType Clone(Cloner cloner) {
    return new DefaultValueExpressionType(cloner, this);
  }

  protected override Dictionary<TypeParameter, Type> GetTypeMap() {
    return typeMap;
  }
}

public class DefaultValueExpressionPreType : DefaultValueExpression, ICloneable<DefaultValueExpressionPreType> {
  private readonly Dictionary<TypeParameter, PreType> preTypeMap;

  public DefaultValueExpressionPreType(IOrigin tok, Formal formal,
    Expression/*?*/ receiver, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, PreType> preTypeMap)
    : base(tok, formal, receiver, substMap) {
    this.preTypeMap = preTypeMap;
  }

  public DefaultValueExpressionPreType(Cloner cloner, DefaultValueExpressionPreType original) : base(cloner, original) {
    preTypeMap = original.preTypeMap;
  }

  public DefaultValueExpressionPreType Clone(Cloner cloner) {
    return new DefaultValueExpressionPreType(cloner, this);
  }

  protected override Dictionary<TypeParameter, Type> GetTypeMap() {
    return preTypeMap.ToDictionary(
      x => x.Key,
      x => PreType2TypeUtil.PreType2FixedType(x.Value));
  }
}
