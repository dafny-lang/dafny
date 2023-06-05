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
using ResolutionContext = Microsoft.Dafny.ResolutionContext;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {

    void ResolveNestedMatchStmt(NestedMatchStmt stmt, ResolutionContext resolutionContext) {
      ResolveExpression(stmt.Source, resolutionContext);

      foreach (var mc in stmt.Cases) {
        ResolveAttributes(mc, resolutionContext, false);

        scope.PushMarker();
        ResolveExtendedPattern(stmt.Source.tok, mc.Pat, stmt.Source.PreType, false, resolutionContext);

        dominatingStatementLabels.PushMarker();
        mc.Body.ForEach(ss => ResolveStatementWithLabels(ss, resolutionContext));
        dominatingStatementLabels.PopMarker();

        scope.PopMarker();
      }
    }

    void ResolveNestedMatchExpr(NestedMatchExpr expr, ResolutionContext resolutionContext) {
      ResolveExpression(expr.Source, resolutionContext);

      expr.PreType = CreatePreTypeProxy("result of match expression");
      foreach (var mc in expr.Cases) {
        ResolveAttributes(mc, resolutionContext, false);

        scope.PushMarker();
        ResolveExtendedPattern(expr.Source.tok, mc.Pat, expr.Source.PreType, false, resolutionContext);

        ResolveExpression(mc.Body, resolutionContext);
        AddSubtypeConstraint(expr.PreType, mc.Body.PreType, mc.Body.tok,
          "type of case bodies do not agree (found {1}, previous types {0})");

        scope.PopMarker();
      }
    }

    /// <summary>
    /// Try to make sure "preType" is not an unresolved proxy. If it is a proxy, then partially solve type constraints in hopes
    /// of resolving it. If that still doesn't resolve it, then report and error and return "false".
    /// Otherwise (that is, upon success), return "true".
    /// </summary>
    bool InsistOnKnowingPreType(IToken tok, PreType preType) {
      if (preType.Normalize() is PreTypeProxy) {
        PartiallySolveTypeConstraints(null, true);

        if (preType.Normalize() is PreTypeProxy) {
          ReportError(tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
          return false;
        }
      }
      return true; // success: preType.Normalize() is a DPreType
    }

    /// <summary>
    /// Resolve "pattern" and push onto "scope" all its bound variables.
    /// </summary>
    public void ResolveExtendedPattern(IToken sourceExprToken, ExtendedPattern pattern, PreType preType, bool inDisjunctivePattern, ResolutionContext resolutionContext) {
      if (pattern is DisjunctivePattern dp) {
        foreach (var alt in dp.Alternatives) {
          ResolveExtendedPattern(sourceExprToken, alt, preType, true, resolutionContext);
        }
        return;
      }

      if (pattern is LitPattern litPattern) {
        var lit = litPattern.OptimisticallyDesugaredLit;
        ResolveExpression(lit, resolutionContext);
        AddSubtypeConstraint(preType, lit.PreType, litPattern.tok,
          "literal pattern (of type {1}) cannot be used with source type {0}");
        return;
      }

      var idPattern = (IdPattern)pattern;
      if (idPattern.Type is not TypeProxy) {
        Contract.Assert(idPattern.Arguments == null); // the parser ensures this condition (the ID cannot be followed by both "(...)" and ": ...")
        resolver.ResolveType(idPattern.Tok, idPattern.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        // When a type is supplied, the ID is understood to be a bound variable.
        ResolveParameterlessIdPattern(idPattern, preType, inDisjunctivePattern, resolutionContext);
        return;
      }

      // Note: If the language were to (be extended to) allow qualified names in patterns, then
      // that qualified name should be resolved here, which also provides its pre-type. Then, that
      // pre-type should be checked to be assignable to "preType". All of this can be done even if
      // "preType" is a proxy.
      // Maybe the language should change to work this way even for non-qualified names. But as it
      // currently stands, "preType" is needed to look up the given ID.
      // (End of Note.)

      if (TryResolvingAsConst(idPattern, preType, false, resolutionContext)) {
        // the ID is a const with a LiteralExpr RHS, so pick it
        return;
      }

      // Use "preType" as a guide to looking up the given ID. This requires knowing what "preType" is.
      if (!InsistOnKnowingPreType(sourceExprToken, preType)) {
        return;
      }
      var dpreType = (DPreType)preType.Normalize();

      if (dpreType.Decl is DatatypeDecl dtd && dtd.ConstructorsByName.TryGetValue(idPattern.Id, out var ctor)) {
        // the given ID is a datatype constructor
        idPattern.Ctor = ctor;
      } else if (idPattern.Arguments == null) {
        // not a datatype constructor, so either a named constant or a bound variable
        ResolveParameterlessIdPattern(idPattern, preType, inDisjunctivePattern, resolutionContext);
        return;
      } else {
        // this is an error; if tuples are involved, specialize the error message
        if (idPattern.Id == BuiltIns.TupleTypeCtorName(1)) {
          ReportError(idPattern.Tok, "parentheses are not allowed around a pattern");
        } else if (idPattern.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
          ReportError(pattern.Tok, $"tuple type does not match type '{preType}'");
        } else {
          ReportError(idPattern.Tok, $"type '{preType}' does not contain a datatype constructor '{idPattern.Id}'");
        }
        return;
      }

      if (idPattern.Arguments == null) {
        if (ctor.Formals.Count == 0) {
          // nullary constructor without () -- so convert it to a constructor
          idPattern.MakeAConstructor();
        } else {
          ReportError(idPattern.Tok, $"constructor '{ctor.Name}' of arity {ctor.Formals.Count} is applied without any arguments");
          return;
        }
      }
      if (idPattern.Arguments.Count != ctor.Formals.Count) {
        ReportError(idPattern.Tok, $"constructor '{ctor.Name}' of arity {ctor.Formals.Count} is applied to {idPattern.Arguments.Count} argument(s)");
        return;
      }

      var subst = PreType.PreTypeSubstMap(dtd.TypeArgs, dpreType.Arguments);
      for (var i = 0; i < idPattern.Arguments.Count; i++) {
        var argumentPreType = ctor.Formals[i].PreType.Substitute(subst);
        ResolveExtendedPattern(sourceExprToken, idPattern.Arguments[i], argumentPreType, inDisjunctivePattern, resolutionContext);
      }
    }

    /// <summary>
    /// Tries to resolve "idPattern" as a symbolic constant with a LiteralExpr RHS.
    ///
    /// Return "true" iff "idPattern" is a symbolic constant with a RHS (regardless of what that RHS is).
    ///
    /// If there is such a RHS and that RHS is a LiteralExpr, then
    ///   * record the RHS literal as "idPattern.ResolvedLit", and
    ///   * constrain its type to be assignable to "preType".
    /// If there is such a RHS, but that RHS is not a LiteralExpr, then
    ///   * report an error, if "reportErrors".
    /// </summary>
    private bool TryResolvingAsConst(IdPattern idPattern, PreType preType, bool reportErrors, ResolutionContext resolutionContext) {
      var e = new NameSegment(idPattern.Tok, idPattern.Id, null);
      ResolveNameSegment(e, true, null, resolutionContext, false, false);
      if (e.ResolvedExpression is MemberSelectExpr { Member: ConstantField { IsStatic: true, Rhs: { } rhs } }) {
        if (rhs is LiteralExpr lit) {
          // the ID refers to a const whose RHS is a literal
          idPattern.ResolvedLit = lit;
          AddSubtypeConstraint(preType, lit.PreType, idPattern.Tok, "literal pattern (of type {1}) cannot be used with source type {0}");
        } else if (reportErrors) {
          ReportError(idPattern.Tok, $"{idPattern.Id} is not initialized as a constant literal");
        }
        return true;
      }
      return false;
    }

    private void ResolveParameterlessIdPattern(IdPattern idPattern, PreType preType, bool inDisjunctivePattern, ResolutionContext resolutionContext) {
      Contract.Requires(idPattern.Arguments == null);

      if (idPattern.Type is TypeProxy) {
        if (TryResolvingAsConst(idPattern, preType, true, resolutionContext)) {
          return;
        }
      }

      // no other options remain; the ID denotes a new bound variable

      if (inDisjunctivePattern) {
        ReportError(idPattern.Tok, "Disjunctive patterns may not bind variables");
      }

      idPattern.BoundVar = new BoundVar(idPattern.Tok, idPattern.Id, idPattern.Type) {
        PreType = Type2PreType(idPattern.Type, "case pattern ID")
      };
      AddSubtypeConstraint(preType, idPattern.BoundVar.PreType, idPattern.Tok,
        "pattern (of type {1}) cannot be used with source type {0}");
      if (!idPattern.IsWildcardPattern) {
        resolver.ScopePushAndReport(scope, idPattern.BoundVar, "parameter");
      }
    }
  }
}
