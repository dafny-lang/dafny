using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class SubsetTypeDecl : TypeSynonymDecl, RedirectingTypeDecl {
  public override string WhatKind { get { return "subset type"; } }
  public readonly BoundVar Var;
  public readonly Expression Constraint;
  public enum WKind { CompiledZero, Compiled, Ghost, OptOut, Special }
  public readonly SubsetTypeDecl.WKind WitnessKind;
  public readonly Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
  [FilledInDuringResolution] public bool ConstraintIsCompilable;
  [FilledInDuringResolution] public bool CheckedIfConstraintIsCompilable = false; // Set to true lazily by the Resolver when the Resolver fills in "ConstraintIsCompilable".
  public SubsetTypeDecl(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module,
    BoundVar id, Expression constraint, WKind witnessKind, Expression witness,
    Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, id.Type, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(typeArgs != null);
    Contract.Requires(module != null);
    Contract.Requires(id != null && id.Type != null);
    Contract.Requires(constraint != null);
    Contract.Requires((witnessKind == WKind.Compiled || witnessKind == WKind.Ghost) == (witness != null));
    Var = id;
    Constraint = constraint;
    Witness = witness;
    WitnessKind = witnessKind;
  }

  public override IEnumerable<Node> Children =>
    base.Children.Concat(new[] { Constraint });

  BoundVar RedirectingTypeDecl.Var { get { return Var; } }
  Expression RedirectingTypeDecl.Constraint { get { return Constraint; } }
  WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
  Expression RedirectingTypeDecl.Witness { get { return Witness; } }

  public override List<Type> ParentTypes(List<Type> typeArgs) {
    return new List<Type> { RhsWithArgument(typeArgs) };
  }
}