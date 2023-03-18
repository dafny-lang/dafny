//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using ResolutionContext = Microsoft.Dafny.ResolutionContext;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {

#if SOON
    /// <summary>
    /// Resolves a NestedMatchExpr by
    /// 0 - resolving the case patterns and case bodies
    /// 1 - desugaring it into a decision tree of MatchExpr and ITEEXpr (for constant matching)
    /// 2 - resolving the generated (sub)expression
    /// </summary>
    void ResolveNestedMatchExpr(NestedMatchExpr me, ResolutionContext resolutionContext) {
      Contract.Requires(me != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(me.ResolvedExpression == null);

      var errorCount = ErrorCount;
      ResolveExpression(me.Source, resolutionContext);
      me.PreType = CreatePreTypeProxy("match result");

      // Ensure that all ExtendedPattern held in NestedMatchCase are linear.
      // Use sourcePreType to determine if IdPatterns are datatypes (of the provided type) or variables.
      foreach (var mc in me.Cases) {
        scope.PushMarker();
        ResolveAttributes(mc, resolutionContext, false);
        ResolveExtendedPattern(mc.Pat, me.Source.PreType, me.Source.tok, resolutionContext,
          (tok, name, ty, pt) => new BoundVar(tok, name, ty) { PreType = pt });
        foreach (var v in mc.Pat.Vars) {
          ScopePushExpectSuccess(v, "bound pattern variable", false);
        }
        ResolveExpression(mc.Body, resolutionContext);
        AddSubtypeConstraint(me.PreType, mc.Body.PreType, mc.Body.tok, "type of case body ({1}) not assignable to type of 'match' ({0})");
        scope.PopMarker();
      }

      if (ErrorCount == errorCount) {
#if SOON
        CompileNestedMatchExpr(me, resolutionContext);
        ResolveExpression(me.ResolvedExpression, resolutionContext);
#endif
      }
    }

    void ResolveNestedMatchStmt(NestedMatchStmt stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      var errorCount = ErrorCount;
      ResolveExpression(stmt.Source, resolutionContext);

      // Ensure that all ExtendedPattern held in NestedMatchCase are linear.
      // Use sourcePreType to determine if IdPatterns are datatypes (of the provided type) or variables.
      foreach (var mc in stmt.Cases) {
        scope.PushMarker();
        ResolveAttributes(mc, resolutionContext, false);
        ResolveExtendedPattern(mc.Pat, stmt.Source.PreType, stmt.Source.tok, resolutionContext,
          (tok, name, ty, pt) => new BoundVar(tok, name, ty) { PreType = pt });
        foreach (var v in mc.Pat.Vars) {
          ScopePushExpectSuccess(v, "bound pattern variable", false);
        }
        foreach (var ss in mc.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
        scope.PopMarker();
      }
    }

    // pat could be
    // 1 - An IdPattern (without argument) at base type
    // 2 - A LitPattern at base type
    // 3* - An IdPattern at tuple type representing a tuple
    // 3 - An IdPattern at datatype type representing a constructor of type
    // 4 - An IdPattern at datatype type with no arguments representing a bound variable
    private void ResolveExtendedPattern(ExtendedPattern pat, PreType preType, IToken sourceTok, ResolutionContext opts,
      Func<IToken, string, Type, PreType, IVariable> createVariable) {
      Contract.Requires(preType != null);

      if (pat is LitPattern litPattern) {
        // The pattern is a literal expression, like 'true' or '-3'
        ResolveExpression(litPattern.OrigLit, opts);
        AddSubtypeConstraint(preType, litPattern.OrigLit.PreType, litPattern.OrigLit.tok,
          "literal (of type {1}) is not a value of the source type ({0})");
        return;
      }

      // We handled the LitPattern case above, so the only remaining case is IdPattern.
      var idpat = (IdPattern)pat;
      // Something parsed as an IdPattern can be one of two things:
      //   - a datatype constructor, like 'Nil' or 'Cons(pat0, pat1)'
      //   - a bound variable, like 'x'
      // It will take some sleuthing to figure out which of these two it is.

      if (idpat.Type is NonProxyType) {
        // an explicit type was given in the input, so this pattern is a variable
        Contract.Assert(idpat.Arguments == null);
        idpat.PreType = Type2PreType(idpat.Type);
        idpat.Var = createVariable(idpat.Tok, idpat.Id, idpat.Type, idpat.PreType);
        AddSubtypeConstraint(idpat.PreType, preType, idpat.Tok,
          "type of source expression ({1}) not assignable to the type of the pattern variable ({0})");
        return;
      }

      // at this point, we're gonna need to consult the type of the source expression
      var sourcePreType = FindDefinedPreType(preType);
      if (sourcePreType == null) {
        ReportError(sourceTok, "Could not resolve the type of the source of the 'match'. Please provide additional typing annotations.");
        return;
      }

      if (sourcePreType.Decl is DatatypeDecl dtd) {
        var ctors = dtd.ConstructorsByName;
        Contract.Assert(ctors != null);
        if (ctors.TryGetValue(idpat.Id, out var ctor)) {
          // the Id in the pattern is a constructor of the source expression's type, so we'll treat the pattern as a constructor
          idpat.Ctor = ctor;
          if (idpat.Arguments == null) {
            // pattern is like a nullary constructor without () -- convert it to a constructor
            idpat.MakeAConstructor();
          }
          if (ctor.Formals.Count != idpat.Arguments.Count) {
            // the source-expression type and the pattern have different numbers of arguments; tailor the error message for tuple types
            if (idpat.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
              ReportError(pat.Tok,
                $"case pattern is a {idpat.Arguments.Count}-element tuple whereas the corresponding 'match' source expression is a {ctor.Formals.Count}-element tuple");
            } else {
              ReportError(pat.Tok, $"case pattern '{idpat.Id}' has {idpat.Arguments.Count} arguments, but expects {ctor.Formals.Count}");
            }
            return;
          }
          var substMap = PreType.PreTypeSubstMap(dtd.TypeArgs, sourcePreType.Arguments);
          for (var i = 0; i < ctor.Formals.Count; i++) {
            var formalPreType = ctor.Formals[i].PreType.Substitute(substMap);
            var patArgument = idpat.Arguments[i];
            ResolveExtendedPattern(patArgument, formalPreType, sourceTok, opts, createVariable);
          }
        } else if (idpat.Arguments != null) {
          // pattern was given with arguments, as if it were a constructor, but we didn't find the name of the constructor when we looked it up
          ReportError(idpat.Tok, $"constructor '{idpat.Id}' not found in type '{sourcePreType}'");
          return;
        } else {
          // pattern is a variable
          idpat.PreType = preType;
          idpat.Var = createVariable(idpat.Tok, idpat.Id, idpat.Type, idpat.PreType);
        }

      } else if (idpat.Arguments == null) {
        // pattern is a variable
        idpat.PreType = preType;
        idpat.Var = createVariable(idpat.Tok, idpat.Id, idpat.Type, idpat.PreType);
      } else if (idpat.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
        ReportError(pat.Tok, $"tuple type does not match type '{preType}'");
      } else {
        ReportError(pat.Tok, $"member '{idpat.Id}' does not exist in type '{preType}'");
      }
    }
#endif

  }
}
