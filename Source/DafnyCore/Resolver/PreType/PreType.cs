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
  
  public abstract class PreType {

    public PreType Normalize() {
      var t = this;
      while (t is PreTypeProxy proxy && proxy.PT != null) {
        t = proxy.PT;
      }
      return t;
    }

    public static bool Same(PreType a, PreType b) {
      a = a.Normalize();
      b = b.Normalize();
      if (a is DPreType ap && b is DPreType bp && ap.Decl == bp.Decl) {
        Contract.Assert(ap.Arguments.Count == bp.Arguments.Count);
        for (var i = 0; i < ap.Arguments.Count; i++) {
          if (!Same(ap.Arguments[i], bp.Arguments[i])) {
            return false;
          }
        }
        return true;
      }
      return a == b;
    }

    public PreType UrAncestor(PreTypeResolver ptResolver) {
      Contract.Requires(ptResolver != null);
      var pt = this;
      while (true) {
        pt = pt.Normalize();
        if (pt is DPreType preType && preType.Decl is NewtypeDecl newtypeDecl) {
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

    public DPreType AsCollectionType() {
      if (Normalize() is DPreType dp) {
        switch (dp.Decl.Name) {
          case "set":
          case "iset":
          case "seq":
          case "multiset":
          case "map":
          case "imap":
            return dp;
          default:
            break;
        }
      }
      return null;
    }

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
      if (!(t is DPreType pt)) {
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
      if (!(t is DPreType pt)) {
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
    public PreType PT; // filled in by resolution

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

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      return this;
    }
  }

  public class DPreType : PreType {
    public readonly TopLevelDecl Decl;
    public readonly List<PreType> Arguments;
    public readonly DPreType PrintablePreType;

    public DPreType(TopLevelDecl decl, List<PreType> arguments, DPreType printablePreType = null) {
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
        var a0 = Arguments[0].Normalize() as DPreType;
        if (Arguments.Count == 2 && (a0 == null || (!IsTupleType(a0.Decl) && !IsArrowType(a0.Decl)))) {
          s = Arguments[0].ToString();
        } else {
          s = $"({Util.Comma(Arguments.GetRange(0, Arguments.Count - 1), arg => arg.ToString())})";
        }
        s += $" ~> {Arguments.Last()}";
      } else if (IsTupleType(Decl)) {
        // TODO: for tuple types, sometimes use prefix "ghost"
        s = $"({Util.Comma(Arguments, arg => arg.ToString())})";
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

    public static bool IsReferenceTypeDecl(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return decl is ClassDecl && !(decl is ArrowTypeDecl);
    }

    public static bool IsArrowType(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return ArrowType.IsArrowTypeName(decl.Name);
    }

    public static bool IsTupleType(TopLevelDecl decl) {
      Contract.Requires(decl != null);
      return BuiltIns.IsTupleTypeName(decl.Name);
    }

    public override PreType Substitute(Dictionary<TypeParameter, PreType> subst) {
      if (Decl is TypeParameter typeParameter) {
        Contract.Assert(Arguments.Count == 0);
        return subst.GetValueOrDefault(typeParameter, this);
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

      return newArguments == null ? this : new DPreType(Decl, newArguments);
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
        var cl = rhsType.ResolvedClass;
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
