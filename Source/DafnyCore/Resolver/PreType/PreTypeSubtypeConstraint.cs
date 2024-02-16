//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  class SubtypeConstraint : OptionalErrorPreTypeConstraint {
    public readonly PreType Super;
    public readonly PreType Sub;

    public override string ErrorMessage() {
      return string.Format(ErrorFormatString, Super, Sub);
    }

    public SubtypeConstraint(PreType super, PreType sub, IToken tok, string errorFormatString, PreTypeConstraint baseError = null, bool reportErrors = true)
      : base(tok, errorFormatString, baseError, reportErrors) {
      Contract.Assert(super != null);
      Contract.Assert(sub != null);
      Super = super.Normalize();
      Sub = sub.Normalize();
    }

    public SubtypeConstraint(PreType super, PreType sub, IToken tok, Func<string> errorFormatStringProducer, bool reportErrors = true)
      : base(tok, errorFormatStringProducer, reportErrors) {
      Contract.Assert(super != null);
      Contract.Assert(sub != null);
      Super = super.Normalize();
      Sub = sub.Normalize();
    }

    public SubtypeConstraint Normalize() {
      var super = Super.Normalize();
      var sub = Sub.Normalize();
      if (object.ReferenceEquals(super, Super) && object.ReferenceEquals(sub, Sub)) {
        return this;
      } else {
        return new SubtypeConstraint(super, sub, Token.NoToken, ErrorFormatString, null, ReportErrors);
      }
    }

    public bool Apply(PreTypeConstraints constraints) {
      var super = Super.NormalizeWrtScope();
      var sub = Sub.NormalizeWrtScope();
      var ptSuper = super as DPreType;
      var ptSub = sub as DPreType;
      // In the following explanations, D is assumed to be a type with three
      // type parameters, being co-variant, contra-variant, and non-variant, respectively.
      if (ptSuper != null && ptSub != null) {
        // We're looking at D<a,b,c> :> E<x,y>
        // If E<x,y> can be rewritten as D<f(x,y), g(x,y), h(x,y)>, then
        //     Constrain a :> f(x,y)
        //     Constrain g(x,y) :> b
        //     Constrain c == h(x,y)
        // else report an error
        var arguments = constraints.GetTypeArgumentsForSuperType(ptSuper.Decl, ptSub, false);
        if (arguments != null) {
          Contract.Assert(arguments.Count == ptSuper.Decl.TypeArgs.Count);
          ConstrainTypeArguments(ptSuper.Decl.TypeArgs, ptSuper.Arguments, arguments, tok, this, constraints);
          return true;
        } else if (ReportErrors) {
          constraints.PreTypeResolver.ReportError(tok, ErrorMessage());
          return true;
        }
      } else if (ptSuper != null) {
        // We're looking at D<a,b,c> :> sub
        // If the head of D has no proper subtypes (i.e., it is not a trait), then
        //     Introduce alpha, beta
        //     Constrain sub == D<alpha, beta, c>
        //     Constrain a :> alpha
        //     Constrain beta :> b
        // else do nothing for now
        if (ptSuper.Decl is not TraitDecl) {
          var arguments = CreateProxiesForTypesAccordingToVariance(tok, ptSuper.Decl.TypeArgs, ptSuper.Arguments, false, ReportErrors, constraints);
          var pt = new DPreType(ptSuper.Decl, arguments);
          constraints.AddEqualityConstraint(pt, sub, tok, ErrorFormatString, null, ReportErrors);
          return true;
        }
      } else if (ptSub != null) {
        // We're looking at super :> D<a,b,c>
        // If the head of D has no proper supertypes (i.e., D has no parent traits), then
        //     Introduce alpha, beta
        //     Constrain super == D<alpha, beta, c>
        //     Constrain alpha :> a
        //     Constrain b :> beta
        // else do nothing for now
        if (PreTypeResolver.HasTraitSupertypes(ptSub)) {
          // there are parent traits
        } else {
          var arguments = CreateProxiesForTypesAccordingToVariance(tok, ptSub.Decl.TypeArgs, ptSub.Arguments, true, ReportErrors, constraints);
          var pt = new DPreType(ptSub.Decl, arguments);
          constraints.AddEqualityConstraint(super, pt, tok, ErrorFormatString, null, ReportErrors);
          return true;
        }
      } else {
        // do nothing for now
      }
      return false;
    }

    /// <summary>
    /// For every non-variant parameters[i], constrain superArguments[i] == subArguments[i].
    /// For every co-variant parameters[i], constrain superArguments[i] :> subArguments[i].
    /// For every contra-variant parameters[i], constrain subArguments[i] :> superArguments[i].
    /// </summary>
    static void ConstrainTypeArguments(List<TypeParameter> parameters, List<PreType> superArguments, List<PreType> subArguments, IToken tok,
      OptionalErrorPreTypeConstraint baseError, PreTypeConstraints constraints) {
      Contract.Requires(parameters.Count == superArguments.Count && superArguments.Count == subArguments.Count);

      for (var i = 0; i < parameters.Count; i++) {
        var tp = parameters[i];
        var arg0 = superArguments[i];
        var arg1 = subArguments[i];
        if (tp.Variance == TypeParameter.TPVariance.Non) {
          constraints.AddEqualityConstraint(arg0, arg1, tok,
            $"non-variant type parameter '{tp.Name}' would require {{0}} = {{1}}", baseError, baseError.ReportErrors);
        } else if (tp.Variance == TypeParameter.TPVariance.Co) {
          constraints.AddSubtypeConstraint(arg0, arg1, tok,
            $"covariant type parameter '{tp.Name}' would require {{0}} :> {{1}}", baseError, baseError.ReportErrors);
        } else {
          constraints.AddSubtypeConstraint(arg1, arg0, tok,
            $"contravariant type parameter '{tp.Name}' would require {{0}} :> {{1}}", baseError, baseError.ReportErrors);
        }
      }
    }

    /// <summary>
    /// For the given arguments: [a0, a1, a2, ...]
    /// use the variance given by parameters: [p0, p1, p2, ...]
    /// to return a list: [t0, t1, t2, ...]
    /// where for each i,
    ///   - if pi is Non, then ai
    ///   - else if (pi is Co) == proxiesAreSupertypes, then a new proxy constrained by:  proxy :> ai
    ///   - else a new proxy constrained by:  ai :> proxy
    /// </summary>
    static List<PreType> CreateProxiesForTypesAccordingToVariance(IToken tok, List<TypeParameter> parameters, List<PreType> arguments,
      bool proxiesAreSupertypes, bool reportErrors, PreTypeConstraints state) {
      Contract.Requires(parameters.Count == arguments.Count);

      if (parameters.All(tp => tp.Variance == TypeParameter.TPVariance.Non)) {
        // special case this common situation
        return arguments;
      }
      var newArgs = new List<PreType>();
      for (var i = 0; i < parameters.Count; i++) {
        var tp = parameters[i];
        if (tp.Variance == TypeParameter.TPVariance.Non) {
          newArgs.Add(arguments[i]);
        } else {
          var co = tp.Variance == TypeParameter.TPVariance.Co ? "co" : "contra";
          var proxy = state.PreTypeResolver.CreatePreTypeProxy($"type used in {co}variance constraint");
          newArgs.Add(proxy);
          if ((tp.Variance == TypeParameter.TPVariance.Co) == proxiesAreSupertypes) {
            state.AddSubtypeConstraint(proxy, arguments[i], tok, "bad", null, reportErrors); // TODO: improve error message
          } else {
            state.AddSubtypeConstraint(arguments[i], proxy, tok, "bad", null, reportErrors); // TODO: improve error message
          }
        }
      }
      return newArgs;
    }
  }

}
