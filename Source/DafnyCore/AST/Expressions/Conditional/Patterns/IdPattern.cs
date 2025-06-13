#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IdPattern : ExtendedPattern, IHasReferences {
  public bool HasParenthesis { get; }
  public String Id;

  public Type? SyntacticType { get; }

  private Type? type;
  public Type Type => type ??= SyntacticType ?? new InferredTypeProxy();

  public IVariable? BoundVar { get; set; } // Only set if there are no arguments

  public List<ExtendedPattern>? Arguments; // null if just an identifier; possibly empty argument list if a constructor call

  public LiteralExpr? ResolvedLit; // null if just an identifier

  [FilledInDuringResolution]
  public DatatypeCtor? Ctor;

  public bool IsWildcardPattern =>
    Arguments == null && Id.StartsWith(WildcardString);

  public bool IsWildcardExact =>
    Arguments == null && Id == WildcardString;

  public const string WildcardString = "_";

  public void MakeAConstructor() {
    this.Arguments = [];
  }

  public IdPattern(Cloner cloner, IdPattern original) : base(cloner.Origin(original.Origin), original.IsGhost) {
    Id = original.Id;
    Arguments = original.Arguments?.Select(cloner.CloneExtendedPattern).ToList();
    HasParenthesis = original.HasParenthesis;
    SyntacticType = original.SyntacticType;
    if (cloner.CloneResolvedFields) {
      type = cloner.CloneType(original.type);
      BoundVar = cloner.CloneIVariable(original.BoundVar, false);
    }
  }

  public IdPattern(IOrigin origin, String id, List<ExtendedPattern>? arguments,
    bool isGhost = false, bool hasParenthesis = false)
    : this(origin, id, null, arguments, isGhost, hasParenthesis) {
    Id = id;
    Arguments = arguments;
    HasParenthesis = hasParenthesis;
  }

  [SyntaxConstructor]
  public IdPattern(IOrigin origin, String id, Type? syntacticType, List<ExtendedPattern>? arguments,
    bool isGhost = false, bool hasParenthesis = false)
    : base(origin, isGhost) {
    Id = id;
    SyntacticType = syntacticType;
    Arguments = arguments;
    HasParenthesis = hasParenthesis;
  }

  public override string ToString() {
    if (Arguments == null || Arguments.Count == 0) {
      return Id;
    } else {
      List<string> cps = Arguments.ConvertAll<string>(x => x.ToString()!);
      return string.Format("{0}({1})", Id, String.Join(", ", cps));
    }
  }

  public override IEnumerable<INode> Children => Arguments ?? Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Children;

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (ResolvedLit != null) {
        yield return ResolvedLit;
      }
      if (Arguments != null) {
        foreach (var alternative in Arguments) {
          foreach (var ee in alternative.SubExpressions) {
            yield return ee;
          }
        }
      }
    }
  }

  public override void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext,
    Type sourceType, bool isGhost, bool inStatementContext,
    bool inPattern, bool inDisjunctivePattern) {

    if (inDisjunctivePattern && ResolvedLit == null && Arguments == null && !IsWildcardPattern) {
      resolver.reporter.Error(MessageSource.Resolver, Origin, "Disjunctive patterns may not bind variables");
    }

    resolver.ResolveType(Origin, Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);

    if (ResolvedLit != null) {
      // we're done
    } else if (Arguments == null) {
      // If the type was not given explicitly, set it to the sourceType
      if (Type.Normalize() is TypeProxy proxy) {
        proxy.T = sourceType;
      }

      if (inStatementContext) {
        var localVariable = new LocalVariable(Origin, Id, null, isGhost) {
          type = Type
        };
        BoundVar = localVariable;
      } else {
        var boundVar = new BoundVar(Origin, Id, Type) {
          IsGhost = isGhost
        };
        BoundVar = boundVar;
      }

      resolver.ConstrainSubtypeRelation(Type, sourceType, Origin,
        "match source type '{1}' not assignable to bound variable (of type '{0}')", Type, sourceType);
      resolver.scope.Push(Id, BoundVar);

    } else if (Ctor != null) {
      var subst = TypeParameter.SubstitutionMap(sourceType.AsDatatype.TypeArgs, sourceType.NormalizeExpand().TypeArgs);
      for (var index = 0; index < Arguments.Count; index++) {
        var argument = Arguments[index];
        var formal = Ctor.Formals[index];
        argument.Resolve(resolver, resolutionContext, formal.Type.Subst(subst),
          isGhost || formal.IsGhost, inStatementContext, true, inDisjunctivePattern);
      }
    }
  }

  public IEnumerable<Reference> GetReferences() {
    return Ctor == null ? Enumerable.Empty<Reference>() : new[] { new Reference(ReportingRange, Ctor) };
  }

  public void CheckLinearVarPattern(Type type, ResolutionContext resolutionContext, ModuleResolver resolver) {
    if (Arguments != null) {
      if (Id == SystemModuleManager.TupleTypeCtorName(1)) {
        resolver.reporter.Error(MessageSource.Resolver, this.Origin, "parentheses are not allowed around a pattern");
      } else {
        resolver.reporter.Error(MessageSource.Resolver, "MemberDoesNotExist", this.Origin, "member {0} does not exist in type {1}", this.Id, type.ToString());
      }
      return;
    }

    if (resolver.scope.FindInCurrentScope(this.Id) != null) {
      resolver.reporter.Error(MessageSource.Resolver, this.Origin, "Duplicate parameter name: {0}", this.Id);
    } else if (IsWildcardPattern) {
      // Wildcard, ignore
      return;
    } else {
      NameSegment e = new NameSegment(this.Origin, this.Id, null);
      resolver.ResolveNameSegment(e, true, null, resolutionContext, false, false);
      if (e.ResolvedExpression == null) {
        resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Origin, this.Id, type), "parameter");
      } else {
        // finds in full scope, not just current scope
        if (e.Resolved is MemberSelectExpr mse) {
          if (mse.Member.IsStatic && mse.Member is ConstantField cf) {
            Expression? c = cf.Rhs;
            if (c is LiteralExpr lit) {
              this.ResolvedLit = lit;
              if (type.Equals(e.ResolvedExpression.Type)) {
                // OK - type is correct
              } else {
                // may well be a proxy so add a type constraint
                resolver.ConstrainSubtypeRelation(e.ResolvedExpression.Type, type, this.Origin,
                  "the type of the pattern ({0}) does not agree with the match expression ({1})", e.ResolvedExpression.Type, type);
              }
            } else {
              resolver.reporter.Error(MessageSource.Resolver, this.Origin, "{0} is not initialized as a constant literal", this.Id);
              resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Origin, this.Id, type), "parameter");
            }
          } else {
            // Not a static const, so just a variable
            resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Origin, this.Id, type), "parameter");
          }
        } else {
          resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Origin, this.Id, type), "parameter");
        }
      }
    }
  }
}
