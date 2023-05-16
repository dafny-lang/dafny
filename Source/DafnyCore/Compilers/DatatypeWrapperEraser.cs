//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Compilers {
  public class DatatypeWrapperEraser {

    public static bool CanBeLeftUninitialized(DafnyOptions options, Type type) {
      if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt) {
        if (dt.GetGroundingCtor().IsGhost) {
          return true;
        }
        if (GetInnerTypeOfErasableDatatypeWrapper(options, dt, out var innerType)) {
          var typeSubst = TypeParameter.SubstitutionMap(dt.TypeArgs, udt.TypeArgs);
          return CanBeLeftUninitialized(options, innerType.Subst(typeSubst));
        }
      }
      return false;
    }

    /// <summary>
    /// Remove any erasable type wrappers and simplify ghost tuple types.
    /// </summary>
    public static Type SimplifyType(DafnyOptions options, Type ty, bool keepConstraints = false) {
      Contract.Requires(ty != null);
      Contract.Requires(ty is not TypeProxy);

      ty = ty.NormalizeExpand(keepConstraints);
      Contract.Assert(ty is NonProxyType);

      if (ty is UserDefinedType udt) {
        if (udt.ResolvedClass is TupleTypeDecl tupleTypeDecl && tupleTypeDecl.NonGhostTupleTypeDecl != null) {
          var nonGhostTupleTypeDecl = tupleTypeDecl.NonGhostTupleTypeDecl;
          var typeArgsForNonGhostTuple = new List<Type>();
          var n = tupleTypeDecl.TypeArgs.Count;
          Contract.Assert(tupleTypeDecl.ArgumentGhostness.Count == n);
          Contract.Assert(udt.TypeArgs.Count == n);
          for (var i = 0; i < n; i++) {
            if (!tupleTypeDecl.ArgumentGhostness[i]) {
              typeArgsForNonGhostTuple.Add(udt.TypeArgs[i]);
            }
          }
          Contract.Assert(typeArgsForNonGhostTuple.Count == nonGhostTupleTypeDecl.Dims);
          Contract.Assert(nonGhostTupleTypeDecl.NonGhostDims == nonGhostTupleTypeDecl.Dims);
          return new UserDefinedType(udt.tok, nonGhostTupleTypeDecl.Name, nonGhostTupleTypeDecl, typeArgsForNonGhostTuple);

        } else if (udt.ResolvedClass is DatatypeDecl datatypeDecl && GetInnerTypeOfErasableDatatypeWrapper(options, datatypeDecl, out var innerType)) {
          var typeSubst = TypeParameter.SubstitutionMap(datatypeDecl.TypeArgs, udt.TypeArgs);
          var stype = innerType.Subst(typeSubst).NormalizeExpand(keepConstraints);
          return SimplifyType(options, stype, keepConstraints);
        }
      }

      // Simplify the type arguments of "ty"
      if (ty.TypeArgs.Count != 0) {
        var simplifiedArguments = ty.TypeArgs.ConvertAll(typeArg => SimplifyType(options, typeArg, keepConstraints));
        if (Enumerable.Range(0, ty.TypeArgs.Count).Any(i => ty.TypeArgs[i].NormalizeExpand(keepConstraints) != simplifiedArguments[i])) {
          ty.ReplaceTypeArguments(simplifiedArguments);
        }
      }
      return ty;
    }

    public enum MemberCompileStatus { Ordinary, Identity, AlwaysTrue }

    public static MemberCompileStatus GetMemberStatus(DafnyOptions options, MemberDecl member) {
      if (member.EnclosingClass is DatatypeDecl dt) {
        if (IsErasableDatatypeWrapper(options, dt, out var dtor) && dtor == member) {
          // "member" is the sole destructor of an erasable datatype wrapper
          return MemberCompileStatus.Identity;
        } else if (member is DatatypeDiscriminator) {
          // a discriminator of an inductive or coinductive datatype
          return dt.Ctors.Count(c => !c.IsGhost) == 1 ? MemberCompileStatus.AlwaysTrue : MemberCompileStatus.Ordinary;
        }
      }

      return MemberCompileStatus.Ordinary;
    }

    /// <summary>
    /// If "dt" is an erasable datatype wrapper (see description of IsErasableDatatypeWrapper), then return "true" and
    /// set the out-parameter to the inner type. Otherwise, return "false" and sets the out-parameter to null.
    /// </summary>
    public static bool GetInnerTypeOfErasableDatatypeWrapper(DafnyOptions options, DatatypeDecl dt, out Type innerType) {
      if (IsErasableDatatypeWrapper(options, dt, out var coreDestructor)) {
        innerType = coreDestructor.Type;
        return true;
      }
      innerType = null;
      return false;
    }

    /// <summary>
    /// This method determines whether or not "dt" is an "erasable datatype wrapper" that can be optimized away during compilation.
    /// First off, this applies only if
    ///   0 -- the compiler supports this kind of optimization (currently, only the C++ compiles does not support the optimization), and
    ///   1 -- the user doesn't disable the optimization from the command-line using /optimizeerasableDatatypeWrappers:0.
    /// To be an erasable wrapper, the datatype has to:
    ///   2 -- be an inductive datatype (not a "codatatype"), and
    ///   3 -- have exactly one non-ghost constructor, and
    ///   4 -- that constructor must have exactly one non-ghost destructor parameter (say, "d" of type "D"), and
    ///   5 -- have no fields declared as members, and
    ///   6 -- the compiled parts of type "D" must not include the datatype itself, and
    ///   7 -- not be declared with {:extern} (since extern code may rely on it being there).
    ///
    /// If the conditions above apply, then the method returns true and sets the out-parameter to the core DatatypeDestructor "d".
    /// From this return, the compiler (that is, the caller) will arrange to compile type "dt" as type "D".
    /// If according to the conditions above, "dt" is not an erasable wrapper, the method returns false; the out-parameter should
    /// then not be used by the caller.
    /// </summary>
    public static bool IsErasableDatatypeWrapper(DafnyOptions options, DatatypeDecl dt, out DatatypeDestructor coreDestructor) {
      if (options.Backend.SupportsDatatypeWrapperErasure && options.Get(CommonOptionBag.OptimizeErasableDatatypeWrapper)) {
        // First, check for all conditions except the non-cycle condition
        if (FindUnwrappedCandidate(options, dt, out var candidateCoreDestructor)) {
          // Now, check if the type of the destructor contains "datatypeDecl" itself
          if (!CompiledTypeContains(options, candidateCoreDestructor.Type, dt, ImmutableHashSet<TopLevelDecl>.Empty)) {
            coreDestructor = candidateCoreDestructor;
            return true;
          }
        }
      }
      coreDestructor = null;
      return false;
    }

    /// <summary>
    /// Check for conditions 2, 3, 4, 5, and 7 (but not 0, 1, and 6) mentioned in the description of IsErasableDatatypeWrapper.
    /// </summary>
    private static bool FindUnwrappedCandidate(DafnyOptions options, DatatypeDecl datatypeDecl, out DatatypeDestructor coreDtor) {
      if (datatypeDecl is IndDatatypeDecl &&
          !datatypeDecl.IsExtern(options, out _, out _) &&
          !datatypeDecl.Members.Any(member => member is Field)) {
        var nonGhostConstructors = datatypeDecl.Ctors.Where(ctor => !ctor.IsGhost).ToList();
        if (nonGhostConstructors.Count == 1) {
          // there is exactly one non-ghost constructor
          var ctor = nonGhostConstructors[0];
          var nonGhostDestructors = ctor.Destructors.Where(dtor => !dtor.IsGhost).ToList();
          if (nonGhostDestructors.Count == 1) {
            // there is exactly one non-ghost parameter to "ctor"
            coreDtor = nonGhostDestructors[0];
            return true;
          }
        }
      }
      coreDtor = null;
      return false;
    }

    /// <summary>
    /// Return "true" if a traversal into the components of "type" finds "lookingFor" before passing through any type in "visited".
    /// "lookingFor" is expected not to be a subset type, and "visited" is expected not to contain any subset types.
    /// </summary>
    private static bool CompiledTypeContains(DafnyOptions options, Type type, TopLevelDecl lookingFor, IImmutableSet<TopLevelDecl> visited) {
      type = type.NormalizeExpand();
      if (type is UserDefinedType udt) {
        if (udt.ResolvedClass == lookingFor) {
          return true;
        }
        if (visited.Contains(udt.ResolvedClass)) {
          return false;
        }
        visited = visited.Union(ImmutableHashSet.Create(udt.ResolvedClass));
        // (a) IF "udt.ResolvedClass" is an erasable type wrapper, then we want to continue the search with
        // its core destructor, suitably substituting type arguments for type parameters.
        // (b) If it is NOT, then we just want to search in its type arguments (like we would for non-UserDefinedType's).
        //
        // However, we don't know which of (a) or (b) we're looking at. So, we first explore (a), and if that
        // shows that the core destructor of "udt.ResolvedClass" has no cycles, then "udt.ResolvedClass" is
        // indeed an erasable type wrapper. If "udt.ResolvedClass" is involved in some cycle, then it is not
        // an erasable type wrapper, so we abandon (a) and instead do (b).
        if (udt.ResolvedClass is DatatypeDecl d && FindUnwrappedCandidate(options, d, out var dtor)) {
          var typeSubst = TypeParameter.SubstitutionMap(d.TypeArgs, udt.TypeArgs);
          if (CompiledTypeContains(options, dtor.Type.Subst(typeSubst), lookingFor, visited)) {
            return true;
          }
        }
      }
      return type.TypeArgs.Any(ty => CompiledTypeContains(options, ty, lookingFor, visited));
    }

  }
}
