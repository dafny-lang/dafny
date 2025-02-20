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

  class EqualityConstraint : OptionalErrorPreTypeConstraint {
    public PreType A;
    public PreType B;

    public EqualityConstraint(PreType a, PreType b, IOrigin tok, string msgFormat, PreTypeConstraint baseError = null, bool reportErrors = true)
      : base(tok, msgFormat, baseError, reportErrors) {
      A = a;
      B = b;
    }

    public override string ErrorMessage() {
      return string.Format(ErrorFormatString, A, B);
    }

    /// <summary>
    /// Constrain "A" to be the same type as "B".
    /// Because this method makes calls that eventually call constraints.DirectionalBounds, it should be
    /// called only when constraints.unnormalizedSubtypeConstraints is in a stable state. That means,
    /// in particular, that this method cannot be called in middle of constraints.ApplySubtypeConstraints.
    /// </summary>
    public IEnumerable<EqualityConstraint> Apply(PreTypeConstraints constraints) {
      var a = A.NormalizeWrtScope();
      var b = B.NormalizeWrtScope();
      if (a == b) {
        // we're already there
      } else if (a is PreTypeProxy pa && !b.Contains(pa, 1, [], constraints, 0)) {
        pa.Set(b);
      } else if (b is PreTypeProxy pb && !a.Contains(pb, 1, [], constraints, 0)) {
        pb.Set(a);
      } else if (a is DPreType da && b is DPreType db && da.Decl == db.Decl) {
        Contract.Assert(da.Arguments.Count == db.Arguments.Count);
        for (var i = 0; i < da.Arguments.Count; i++) {
          // TODO: should the error message in the following line be more specific?
          yield return new EqualityConstraint(da.Arguments[i], db.Arguments[i], tok, ErrorFormatString, null, ReportErrors);
        }
      } else if (ReportErrors) {
        constraints.PreTypeResolver.ReportError(tok, ErrorFormatString, a, b);
      }
    }

  }
}
