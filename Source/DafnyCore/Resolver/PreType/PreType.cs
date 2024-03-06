//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  /// <summary>
  /// A PreType is a Type, but ignoring type synonyms and subset types. That is, to obtain the
  /// pre-type corresponding to a type, expand any type synonym to its RHS and expand any
  /// subset type with its base type.
  ///
  /// A pre-type captures the part of a type that is mutually dependent on name resolution.
  /// That is, name resolution needs to know the pre-type of expressions and pre-type inference
  /// needs to know what names refer to. By separating out the pre-type part of types, the
  /// process of name resolution is simplified.
  ///
  /// See also the description of https://github.com/dafny-lang/dafny/pull/3795.
  /// </summary>
  public abstract class PreType {
    public const string TypeNameBool = "bool";
    public const string TypeNameChar = "char";
    public const string TypeNameInt = "int";
    public const string TypeNameReal = "real";
    public const string TypeNameORDINAL = "ORDINAL";
    public const string TypeNameBvPrefix = "bv";
    public const string TypeNameSet = "set";
    public const string TypeNameIset = "iset";
    public const string TypeNameSeq = "seq";
    public const string TypeNameMultiset = "multiset";
    public const string TypeNameMap = "map";
    public const string TypeNameImap = "imap";
    public const string TypeNameObjectQ = "object?";
    public const string TypeNameArray = "array";

    public static string SetTypeName(bool finite) => finite ? TypeNameSet : TypeNameIset;
    public static string MapTypeName(bool finite) => finite ? TypeNameMap : TypeNameImap;

    /// <summary>
    /// Normalize() follows the pre-type to which a pre-type proxy has been resolved, if any.
    /// </summary>
    public PreType Normalize() {
      var t = this;
      while (t is PreTypeProxy { PT: { } proxyFor }) {
        t = proxyFor;
      }
      return t;
    }

    /// <summary>
    /// NormalizeWrtScope() does a little more than Normalize(). Namely, if the normalized
    /// pre-type refers to a declaration that is not in scope, then what is returned is a
    /// pre-type around the InternalSynonymDecl that stands for the out-of-scope type.
    /// </summary>
    public PreType NormalizeWrtScope() {
      var t = Normalize();
      if (t is DPreType dPreType) {
        if (dPreType.PrintablePreType != null) {
          dPreType = dPreType.PrintablePreType;
        }
        if (dPreType.Decl is RevealableTypeDecl rtd && !rtd.IsRevealedInScope(Type.GetScope())) {
          return new DPreType(rtd.SynonymInfo.SelfSynonymDecl, dPreType.Arguments, dPreType.PrintablePreType);
        }
      }
      return t;
    }

    public static bool Same(PreType a, PreType b) {
      a = a.Normalize();
      b = b.Normalize();
      if (a is DPreType ap && b is DPreType bp && ap.Decl == bp.Decl) {
        Contract.Assert(ap.Arguments.Count == bp.Arguments.Count);
        return ap.Arguments.Zip(bp.Arguments).All(x => Same(x.First, x.Second));
      }
      return a == b;
    }

    /// <summary>
    /// The "ur-ancestor" of a newtype is the ur-ancestor of its base type.
    /// The ur-ancestor of a non-newtype is the pre-type itself.
    ///
    /// Note, if "this" or any newtype base type encountered in this computation is an unresolved
    /// pre-type proxy, then that pre-type proxy is what is returned. In other words, the search
    /// for the ur-ancestor can only go as far as what proxy information allows.
    ///
    /// It is assumed that this computation does not encounter any cycles.
    /// </summary>
    public PreType UrAncestor(PreTypeResolver ptResolver) {
      Contract.Requires(ptResolver != null);
      var pt = this;
      while (true) {
        pt = pt.Normalize();
        if (pt is DPreType { Decl: NewtypeDecl newtypeDecl } preType) {
          // expand the newtype into its base type
          var subst = PreTypeSubstMap(newtypeDecl.TypeArgs, preType.Arguments);
          var basePreType = ptResolver.Type2PreType(newtypeDecl.BaseType);
          pt = basePreType.Substitute(subst);
        } else {
          // nothing more we can do
          return pt;
        }
      }
    }

    public DPreType AsCollectionPreType() {
      if (Normalize() is DPreType dp) {
        switch (dp.Decl.Name) {
          case TypeNameSet:
          case TypeNameIset:
          case TypeNameSeq:
          case TypeNameMultiset:
          case TypeNameMap:
          case TypeNameImap:
            return dp;
          default:
            break;
        }
      }
      return null;
    }

    public bool IsRefType => Normalize() is DPreType { Decl: ClassLikeDecl { IsReferenceTypeDecl: true } };

    /// <summary>
    /// Returns "true" if "proxy" is among the free variables of "this".
    /// "proxy" is expected to be normalized.
    ///
    /// Parameter "recursionDepth" is used as a safe-guarding against infinite (or excessively large) recursion.
    /// It's not expected to ever happen, but it seems better to check at run time rather than risk hanging.
    /// </summary>
    public abstract bool Contains(PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited, PreTypeConstraints constraints, int recursionDepth);

    public static Dictionary<TypeParameter, PreType> PreTypeSubstMap(List<TypeParameter> parameters, List<PreType> arguments) {
      Contract.Requires(parameters.Count == arguments.Count);
      var subst = new Dictionary<TypeParameter, PreType>();
      for (var i = 0; i < parameters.Count; i++) {
        subst.Add(parameters[i], arguments[i]);
      }
      return subst;
    }

    /// <summary>
    /// If the substitution has no effect, the return value is pointer-equal to 'this'
    /// </summary>
    public abstract PreType Substitute(Dictionary<TypeParameter, PreType> subst);

    public bool IsLeafType() {
      var t = Normalize();
      if (t is not DPreType pt) {
        return false;
      } else if (pt.Decl is TraitDecl) {
        return false;
      }
      // Now, it comes down to the type arguments
      Contract.Assert(pt.Decl.TypeArgs.Count == pt.Arguments.Count);
      for (var i = 0; i < pt.Decl.TypeArgs.Count; i++) {
        switch (pt.Decl.TypeArgs[i].Variance) {
          case TypeParameter.TPVariance.Non:
            // this is fine for a leaf
            break;
          case TypeParameter.TPVariance.Co:
            if (!pt.Arguments[i].IsLeafType()) {
              return false;
            }
            break;
          case TypeParameter.TPVariance.Contra:
            if (!pt.Arguments[i].IsRootType()) {
              return false;
            }
            break;
        }
      }
      return true;
    }

    public bool IsRootType() {
      var t = Normalize();
      if (t is not DPreType pt) {
        return false;
      } else if (PreTypeResolver.HasTraitSupertypes(pt)) {
        return false;
      }
      // Now, it comes down to the type arguments
      Contract.Assert(pt.Decl.TypeArgs.Count == pt.Arguments.Count);
      for (var i = 0; i < pt.Decl.TypeArgs.Count; i++) {
        switch (pt.Decl.TypeArgs[i].Variance) {
          case TypeParameter.TPVariance.Non:
            // this is fine for a root
            break;
          case TypeParameter.TPVariance.Co:
            if (!pt.Arguments[i].IsRootType()) {
              return false;
            }
            break;
          case TypeParameter.TPVariance.Contra:
            if (!pt.Arguments[i].IsLeafType()) {
              return false;
            }
            break;
        }
      }
      return true;
    }
  }

  public class PreTypeProxy : PreType {
    public readonly int UniqueId;

    [FilledInDuringResolution] public PreType PT { get; private set; }

    /// <summary>
    /// There should be just one call to this constructor, namely from PreTypeResolver.CreatePreTypeProxy.
    /// Other callers that need a new pre-type proxy should call PreTypeResolver.CreatePreTypeProxy.
    /// </summary>
    public PreTypeProxy(int uniqueId) {
      UniqueId = uniqueId;
    }

    public override string ToString() {
      return PT != null ? PT.ToString() : "?" + UniqueId;
    }

    /// <summary>
    /// Expects PT to be null, and sets PT to the given "target". Assumes that the caller has performed an
    /// occurs check.
    /// </summary>
    public void Set(PreType target) {
      Contract.Requires(target != null);
      Contract.Requires(PT == null);
      Contract.Assert(PT == null); // make sure we get a run-time check for this important condition
      PT = target;
    }

    public override bool Contains(PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited, PreTypeConstraints constraints, int recursionDepth) {
      if (this == proxy) {
        return true;
      }
      if (PT != null) {
        return PT.Contains(proxy, direction, visited, constraints, recursionDepth);
      }
      if (visited.Add(this)) {
        return constraints.DirectionalBounds(this, direction).Any(su => su.Contains(proxy, direction, visited, constraints, recursionDepth));
      }
      return false;
    }

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      if (PT != null) {
        return PT.Substitute(subst);
      } else {
        return this;
      }
    }
  }

  public class DPreType : PreType {
    public readonly TopLevelDecl Decl;
    public readonly List<PreType> Arguments;
    public readonly DPreType PrintablePreType;

    public DPreType(TopLevelDecl decl, List<PreType> arguments, DPreType printablePreType = null) {
      Contract.Requires(decl.TypeArgs.Count == arguments.Count);
      Contract.Assume(decl != null);
      Decl = decl;
      Arguments = arguments;
      PrintablePreType = printablePreType;
    }

    public override string ToString() {
      if (PrintablePreType != null) {
        return PrintablePreType.ToString();
      }

      var name = Decl.Name;
      string s;
      if (IsArrowType(Decl)) {
        s = AnyArrowTypeToString("~>");
      } else if (ArrowType.IsPartialArrowTypeName(Decl.Name)) {
        s = AnyArrowTypeToString("-->");
      } else if (ArrowType.IsTotalArrowTypeName(Decl.Name)) {
        s = AnyArrowTypeToString("->");
      } else if (IsTupleType(Decl)) {
        var tupleTypeDecl = (TupleTypeDecl)Decl;
        Contract.Assert(Arguments.Count == tupleTypeDecl.ArgumentGhostness.Count);
        s = Arguments.Zip(tupleTypeDecl.ArgumentGhostness).Comma(argAndGhost =>
          (argAndGhost.Second ? "ghost " : "") + argAndGhost.First.ToString()
        );
        s = "(" + s + ")";
      } else {
        if (IsReferenceTypeDecl(Decl)) {
          name = name + "?";
        }
        if (Arguments.Count == 0) {
          s = name;
        } else {
          s = $"{name}<{Util.Comma(Arguments, arg => arg.ToString())}>";
        }
      }

      return s;
    }

    private string AnyArrowTypeToString(string arrow) {
      string s;
      var a0 = Arguments[0].Normalize() as DPreType;
      if (Arguments.Count == 2 && (a0 == null || (!IsTupleType(a0.Decl) && !IsArrowType(a0.Decl)))) {
        s = Arguments[0].ToString();
      } else {
        s = $"({Util.Comma(Arguments.GetRange(0, Arguments.Count - 1), arg => arg.ToString())})";
      }
      s += $" {arrow} {Arguments.Last()}";
      return s;
    }

    public static bool IsReferenceTypeDecl(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return decl is ClassLikeDecl { IsReferenceTypeDecl: true };
    }

    public static bool IsArrowType(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return ArrowType.IsArrowTypeName(decl.Name);
    }

    public static bool IsTupleType(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return SystemModuleManager.IsTupleTypeName(decl.Name);
    }

    public override bool Contains(PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited, PreTypeConstraints constraints, int recursionDepth) {
      if (recursionDepth == 20) {
        Contract.Assume(false);  // possible infinite recursion
      }
      recursionDepth++;

      var polarities = Decl.TypeArgs.ConvertAll(tp => TypeParameter.Direction(tp.Variance));
      Contract.Assert(polarities != null);
      Contract.Assert(polarities.Count <= Arguments.Count);
      for (int i = 0; i < polarities.Count; i++) {
        if (Arguments[i].Contains(proxy, direction * polarities[i], visited, constraints, recursionDepth)) {
          return true;
        }
      }
      return false;
    }

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      DPreType printablePreType = (DPreType)PrintablePreType?.Substitute(subst);

      if (Decl is TypeParameter typeParameter) {
        Contract.Assert(Arguments.Count == 0);
        var afterSubstitution = subst.GetValueOrDefault(typeParameter, this);
        if (printablePreType == null) {
          return afterSubstitution;
        } else if (printablePreType == PrintablePreType && afterSubstitution == this) {
          return this;
        } else if (afterSubstitution is DPreType dPreType) {
          return new DPreType(dPreType.Decl, dPreType.Arguments, printablePreType);
        } else {
          // TODO: it would be nice to have a place to include "printablePreType" as part of what's returned, but currently only DPreType allows that
          return afterSubstitution;
        }
      }

      // apply substitutions to arguments
      List<PreType> newArguments = null; // allocate the new list lazily
      for (var i = 0; i < Arguments.Count; i++) {
        var arg = Arguments[i];
        var pt = arg.Substitute(subst);
        if (pt != arg && newArguments == null) {
          // lazily construct newArguments
          newArguments = new();
          // copy all previous items, all of which were unaffected by substitution
          for (var j = 0; j < i; j++) {
            newArguments.Add(Arguments[j]);
          }
        }
        if (newArguments != null) {
          newArguments.Add(pt);
        }
      }

      if (newArguments == null && printablePreType == PrintablePreType) {
        return this;
      }
      return new DPreType(Decl, newArguments ?? Arguments, printablePreType);
    }

    /// <summary>
    /// Returns the pre-type "parent<X>", where "X" is a list of type parameters that makes "parent<X>" a supertype of "this".
    /// Requires "this" to be some pre-type "C<Y>" and "parent" to be among the reflexive, transitive parent traits of "C".
    /// </summary>
    public DPreType AsParentType(TopLevelDecl parent, PreTypeResolver preTypeResolver) {
      Contract.Requires(parent != null);
      Contract.Requires(preTypeResolver != null);

      var decl = Decl;
      if (decl is InternalTypeSynonymDecl isyn) {
        var rhsType = isyn.Rhs as UserDefinedType;
        // we expect the .RHS of an InternalTypeSynonymDecl to be a UserDefinedType whose type arguments
        // are exactly the type parameters
        Contract.Assert(rhsType != null);
        TopLevelDeclWithMembers cl;
        if (rhsType.ResolvedClass is NonNullTypeDecl nntd) {
          cl = (TopLevelDeclWithMembers)nntd.ViewAsClass;
        } else {
          cl = (TopLevelDeclWithMembers)rhsType.ResolvedClass;
        }

        Contract.Assert(isyn.TypeArgs.Count == cl.TypeArgs.Count);
        for (var i = 0; i < isyn.TypeArgs.Count; i++) {
          var typeParameter = isyn.TypeArgs[i];
          Contract.Assert(typeParameter == cl.TypeArgs[i]);
          Contract.Assert(rhsType.TypeArgs[i] is UserDefinedType { ResolvedClass: var tpDecl } && tpDecl == typeParameter);
        }

        decl = cl;
      }
      if (decl == parent) {
        return this;
      }
      var typeMapParents = ((TopLevelDeclWithMembers)decl).ParentFormalTypeParametersToActuals;
      var typeMap = PreTypeSubstMap(decl.TypeArgs, Arguments);
      var typeArgs = parent.TypeArgs.ConvertAll(tp => preTypeResolver.Type2PreType(typeMapParents[tp]).Substitute(typeMap));
      return new DPreType(parent, typeArgs);
    }
  }

  /// <summary>
  /// A PreTypePlaceholder is used to fill in the .PreType field of an AST expression node that does not
  /// correspond to an expression. In particular, such an AST node can refer to a module or a type (and,
  /// in a legal program, is syntactically followed by ".X", which will make it an expression).
  /// </summary>
  public abstract class PreTypePlaceholder : PreType {
    public override bool Contains(PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited, PreTypeConstraints constraints, int recursionDepth) {
      throw new NotImplementedException();
    }

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      throw new NotImplementedException();
    }
  }

  public class PreTypePlaceholderModule : PreTypePlaceholder {
  }

  public class PreTypePlaceholderType : PreTypePlaceholder {
  }

  public class UnusedPreType : PreTypePlaceholder {
    public readonly string Why;

    public UnusedPreType(string why) {
      Why = why;
    }

    public override string ToString() {
      return $"(unused -- {Why})";
    }
  }

}
