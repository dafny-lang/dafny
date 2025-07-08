using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// This class is used only inside the resolver itself. It gets hung in the AST in uncompleted name segments.
/// </summary>
class ResolverIdentifierExpr : Expression, IHasReferences, ICloneable<ResolverIdentifierExpr> {
  public TopLevelDecl Decl;
  public List<Type> TypeArgs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Decl != null);
    Contract.Invariant(TypeArgs != null);
    Contract.Invariant(TypeArgs.Count == Decl.TypeArgs.Count);
    Contract.Invariant(Type is ResolverTypeModule or ResolverTypeType);
  }

  public ResolverIdentifierExpr(Cloner cloner, ResolverIdentifierExpr original) : base(cloner, original) {
    Decl = original.Decl;
    TypeArgs = original.TypeArgs;
  }

  public override IEnumerable<INode> Children => TypeArgs.SelectMany(ta => ta.Nodes);

  public abstract class ResolverType : Type {
    public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl>/*?*/ visitedDatatypes) {
      return false;
    }
    public override Type Subst(IDictionary<TypeParameter, Type> subst) {
      throw new NotSupportedException();
    }

    public override Type ReplaceTypeArguments(List<Type> arguments) {
      throw new NotSupportedException();
    }
  }
  public class ResolverTypeModule : ResolverType {
    [System.Diagnostics.Contracts.Pure]
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);
      return "#module";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is ResolverTypeModule;
    }
  }
  public class ResolverTypeType : ResolverType {
    [System.Diagnostics.Contracts.Pure]
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);
      return "#type";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is ResolverTypeType;
    }
  }

  public ResolverIdentifierExpr(IOrigin origin, TopLevelDecl decl, List<Type> typeArgs)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(decl != null);
    Contract.Requires(typeArgs != null && typeArgs.Count == decl.TypeArgs.Count);
    Decl = decl;
    TypeArgs = typeArgs;
    Type = decl is ModuleDecl ? (Type)new ResolverTypeModule() : new ResolverTypeType();
    PreType = decl is ModuleDecl ? new PreTypePlaceholderModule() : new PreTypePlaceholderType();
  }
  public ResolverIdentifierExpr(IOrigin origin, TypeParameter tp)
    : this(origin, tp, []) {
    Contract.Requires(origin != null);
    Contract.Requires(tp != null);
  }

  public IEnumerable<Reference> GetReferences() {
    return new[] { new Reference(ReportingRange, Decl) };
  }

  public ResolverIdentifierExpr Clone(Cloner cloner) {
    return new ResolverIdentifierExpr(cloner, this);
  }
}