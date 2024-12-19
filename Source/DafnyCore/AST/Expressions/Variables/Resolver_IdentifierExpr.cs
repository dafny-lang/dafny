using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// This class is used only inside the resolver itself. It gets hung in the AST in uncompleted name segments.
/// </summary>
class Resolver_IdentifierExpr : Expression, IHasReferences, ICloneable<Resolver_IdentifierExpr> {
  public readonly TopLevelDecl Decl;
  public readonly List<Type> TypeArgs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Decl != null);
    Contract.Invariant(TypeArgs != null);
    Contract.Invariant(TypeArgs.Count == Decl.TypeArgs.Count);
    Contract.Invariant(Type is ResolverType_Module || Type is ResolverType_Type);
  }

  public Resolver_IdentifierExpr(Cloner cloner, Resolver_IdentifierExpr original) : base(cloner, original) {
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
  public class ResolverType_Module : ResolverType {
    [System.Diagnostics.Contracts.Pure]
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);
      return "#module";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is ResolverType_Module;
    }
  }
  public class ResolverType_Type : ResolverType {
    [System.Diagnostics.Contracts.Pure]
    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      Contract.Assert(parseAble == false);
      return "#type";
    }
    public override bool Equals(Type that, bool keepConstraints = false) {
      return that.NormalizeExpand(keepConstraints) is ResolverType_Type;
    }
  }

  public Resolver_IdentifierExpr(IOrigin tok, TopLevelDecl decl, List<Type> typeArgs)
    : base(tok) {
    Contract.Requires(tok != null);
    Contract.Requires(decl != null);
    Contract.Requires(typeArgs != null && typeArgs.Count == decl.TypeArgs.Count);
    Decl = decl;
    TypeArgs = typeArgs;
    Type = decl is ModuleDecl ? (Type)new ResolverType_Module() : new ResolverType_Type();
    PreType = decl is ModuleDecl ? new PreTypePlaceholderModule() : new PreTypePlaceholderType();
  }
  public Resolver_IdentifierExpr(IOrigin tok, TypeParameter tp)
    : this(tok, tp, new List<Type>()) {
    Contract.Requires(tok != null);
    Contract.Requires(tp != null);
  }

  public IEnumerable<Reference> GetReferences() {
    return new[] { new Reference(Tok, Decl) };
  }

  public Resolver_IdentifierExpr Clone(Cloner cloner) {
    return new Resolver_IdentifierExpr(cloner, this);
  }
}