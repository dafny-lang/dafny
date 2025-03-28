#nullable enable

using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class CollectionType : NonProxyType {
  public abstract string CollectionTypeName { get; }
  public override IEnumerable<Node> Nodes => TypeArgs.SelectMany(ta => ta?.Nodes ?? []);

  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    var targs = HasTypeArg() ? this.TypeArgsToString(options, context, parseAble) : "";
    return CollectionTypeName + targs;
  }

  // This override enables CollectionType's SyntaxConstructor to accept typeArgs,
  // without needing to refactor NonProxyType's SyntaxConstructor to do so too.
  public sealed override List<Type?> TypeArgs { get; set; } = [];

  /// <summary>
  /// Denotes the primary element type. (For a map, this is the domain.)
  /// </summary>
  [FilledInDuringResolution] public Type Arg => arg!;
  private Type? arg;

  public Type? ValueArg => TypeArgs.Last();

  // The following methods, HasTypeArg and SetTypeArg/SetTypeArgs, are to be called during resolution to make sure that "arg" becomes set.
  public bool HasTypeArg() {
    return arg != null;
  }

  public void SetTypeArg(Type typeArg) {
    Contract.Assume(arg == null);  // Can only set it once.  This is really a precondition.
    arg = typeArg;

    Debug.Assert(TypeArgs.Count == 0);
    TypeArgs.Add(typeArg);
  }

  public virtual void SetTypeArgs(Type typeArg, Type otherTypeArg) {
    Contract.Assume(arg == null);  // Can only set it once.  This is really a precondition.
    arg = typeArg;

    Debug.Assert(TypeArgs.Count == 0);
    TypeArgs.Add(typeArg);
    TypeArgs.Add(otherTypeArg);
  }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    // Contract.Invariant(Contract.ForAll(TypeArgs, tp => tp != null));
    // After resolution, the following is invariant:  Contract.Invariant(Arg != null);
    // However, it may not be true until then.
  }

  /// <summary>
  /// Construct a collection type with either 1 or 2 type arguments.
  /// </summary>
  [SyntaxConstructor]
  protected CollectionType(IOrigin? origin, List<Type?> typeArgs) : base(origin) {
    Contract.Requires(typeArgs is [_] or [null, null] or [not null, not null]);
    arg = typeArgs.FirstOrDefault();
    if (typeArgs is [not null] or [not null, not null]) {
      TypeArgs = typeArgs;
    }
  }

  /// <summary>
  /// This constructor is a collection types with 1 type argument
  /// </summary>
  protected CollectionType(Type? arg) {
    this.arg = arg;
    TypeArgs = new List<Type?>(1);
    if (arg != null) {
      TypeArgs.Add(arg);
    }
  }

  /// <summary>
  /// This constructor is a collection types with 2 type arguments
  /// </summary>
  protected CollectionType(Type? arg, Type? other) {
    this.arg = arg;
    TypeArgs = new List<Type?>(2);
    if (arg != null && other != null) {
      TypeArgs.Add(arg);
      TypeArgs.Add(other);
    }
    Debug.Assert(arg == null && other == null || arg != null && other != null);
  }

  protected CollectionType(Cloner cloner, CollectionType original) {
    arg = cloner.CloneType(original.arg);
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    return Arg.ComputeMayInvolveReferences(visitedDatatypes);
  }

  /// <summary>
  /// This property returns the ResolvedOpcode for the "in" operator when used with this collection type.
  /// </summary>
  public abstract BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn { get; }

  /// <summary>
  /// For a given "source", denoting an expression of this CollectionType, return the BoundedPool corresponding
  /// to an expression "x in source".
  /// </summary>
  public abstract CollectionBoundedPool GetBoundedPool(Expression source);
}