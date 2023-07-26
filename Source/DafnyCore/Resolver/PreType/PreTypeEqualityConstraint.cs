//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {

  class EqualityConstraint : PreTypeStateWithErrorMessage {
    public PreType A;
    public PreType B;

    public EqualityConstraint(PreType a, PreType b, IToken tok, string msgFormat)
      : base(tok, msgFormat) {
      A = a;
      B = b;
    }

    public override string ErrorMessage() {
      return string.Format(ErrorFormatString, A, B);
    }

    /// <summary>
    /// Constrain "A" to be the same type as "B".
    /// Because this method make calls that eventually call preTypeResolver.DirectionalBounds, it should be
    /// called only when preTypeResolver.unnormalizedSubtypeConstraints is in a stable state. That means,
    /// in particular, that this method cannot be called in middle of preTypeResolver.ApplySubtypeConstraints.
    /// </summary>
    public IEnumerable<EqualityConstraint> Apply(PreTypeResolver preTypeResolver) {
      var a = A.Normalize();
      var b = B.Normalize();
      if (a == b) {
        // we're already there
      } else if (a is PreTypeProxy pa && !Occurs(pa, b, preTypeResolver)) {
        pa.Set(b);
      } else if (b is PreTypeProxy pb && !Occurs(pb, a, preTypeResolver)) {
        pb.Set(a);
      } else if (a is DPreType da && b is DPreType db && da.Decl == db.Decl) {
        Contract.Assert(da.Arguments.Count == db.Arguments.Count);
        for (var i = 0; i < da.Arguments.Count; i++) {
          // TODO: should the error message in the following line be more specific?
          yield return new EqualityConstraint(da.Arguments[i], db.Arguments[i], tok, ErrorFormatString);
        }
      } else {
        preTypeResolver.ReportError(tok, ErrorFormatString, a, b);
      }
    }

    /// <summary>
    /// Returns "true" if "proxy" is among the free variables of "t".
    /// "proxy" is expected to be normalized.
    /// </summary>
    private static bool Occurs(PreTypeProxy proxy, PreType t, PreTypeResolver preTypeResolver) {
      return Reaches(t, proxy, 1, new HashSet<PreTypeProxy>(), preTypeResolver, 0);
    }

    /// <summary>
    /// Parameter "recursionDepth" is used as a safe-guarding against infinite (or excessively large) recursion.
    /// It's not expected to happen ever, but it seems better to check at run time rather than risk hanging.
    /// </summary>
    private static bool Reaches(PreType t, PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited,
      PreTypeResolver preTypeResolver, int recursionDepth) {
      if (recursionDepth == 20) {
        Contract.Assume(false);  // possible infinite recursion
      }
      var b = ReachesAux(t, proxy, direction, visited, preTypeResolver, recursionDepth + 1);
      return b;
    }

    private static bool ReachesAux(PreType t, PreTypeProxy proxy, int direction, HashSet<PreTypeProxy> visited,
      PreTypeResolver preTypeResolver, int recursionDepth) {
      t = t.Normalize();
      var tproxy = t as PreTypeProxy;
      if (tproxy == null) {
        var dp = (DPreType)t;
        var polarities = dp.Decl.TypeArgs.ConvertAll(tp => TypeParameter.Direction(tp.Variance));
        Contract.Assert(polarities != null);
        Contract.Assert(polarities.Count <= dp.Arguments.Count);
        for (int i = 0; i < polarities.Count; i++) {
          if (Reaches(dp.Arguments[i], proxy, direction * polarities[i], visited, preTypeResolver, recursionDepth)) {
            return true;
          }
        }
        return false;
      } else if (tproxy == proxy) {
        return true;
      } else if (visited.Contains(tproxy)) {
        return false;
      } else {
        visited.Add(tproxy);
        return preTypeResolver.DirectionalBounds(tproxy, direction).Any(su =>
          Reaches(su, proxy, direction, visited, preTypeResolver, recursionDepth));
      }
    }

  }
}
