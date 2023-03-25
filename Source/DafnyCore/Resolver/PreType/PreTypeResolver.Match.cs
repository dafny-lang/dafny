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

      if (stmt.Source.PreType.Normalize() is PreTypeProxy) {
        PartiallySolveTypeConstraints(null, true);

        if (stmt.Source.PreType.Normalize() is PreTypeProxy) {
          ReportError(stmt.Tok, "Could not resolve the type of the source of the match expression. Please provide additional typing annotations.");
          return;
        }
      }
      var sourcePreType = (DPreType)stmt.Source.PreType.Normalize();

      var subst = PreType.PreTypeSubstMap(sourcePreType.Decl.TypeArgs, sourcePreType.Arguments);
      foreach (NestedMatchCaseStmt mc in stmt.Cases) {
        scope.PushMarker();
        ResolveAttributes(mc, resolutionContext, false);
        CheckLinearExtendedPattern(mc.Pat, sourcePreType, resolutionContext);
        ResolveMatchCaseStmt(mc, sourcePreType, subst, resolutionContext);
        scope.PopMarker();
      }
    }

    /*
    *  Ensures that all ExtendedPattern held in NestedMatchCase are linear.
    *  Uses provided pre-type to determine if IdPatterns are datatypes (of the provided type) or variables
    *  pat could be
    *  0 - A DisjunctivePattern
    *  1 - An IdPattern (without argument) at base type
    *  2 - A LitPattern at base type
    *  3* - An IdPattern at tuple type representing a tuple
    *  3 - An IdPattern at datatype type representing a constructor of type
    *  4 - An IdPattern at datatype type with no arguments representing a bound variable
    */
    public void CheckLinearExtendedPattern(ExtendedPattern pat, DPreType sourcePreType, ResolutionContext resolutionContext) {
#if SOON
      if (sourcePreType == null) {
        return;
      }

      if (pat is DisjunctivePattern dp) {
        /* =[0]= */
        foreach (var alt in dp.Alternatives) {
          // Pushing a scope silences the “duplicate parameter” error in
          // `CheckLinearVarPattern`.  This is acceptable because disjunctive
          // patterns are not allowed to bind variables (the corresponding
          // error is raised in `RemoveDisjunctivePatterns`).
          resolver.scope.PushMarker();
          CheckLinearExtendedPattern(alt, sourcePreType, resolutionContext);
          resolver.scope.PopMarker();
        }

      } else if (sourcePreType.Decl is not DatatypeDecl) {
        // Neither tuple nor datatype
        if (pat is IdPattern idPattern) {
          if (idPattern.Arguments != null) {
            // pat is a tuple or constructor
            if (idPattern.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
              ReportError(pat.Tok, $"tuple type does not match type '{sourcePreType}'");
            } else {
              ReportError(pat.Tok, $"member '{idPattern.Id}' does not exist in type '{sourcePreType}'");
            }
          } else {
            // pat is a simple variable or a constant
            /* =[1]= */
            CheckLinearVarPattern(idPattern, sourcePreType, resolutionContext);
          }
        } else if (pat is LitPattern) {
          // pat is a literal
          /* =[2]= */
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected ExtendedPattern
        }

      } else if (sourcePreType.Decl is TupleTypeDecl tupleTypeDecl) {
        var udt = sourcePreType.NormalizeExpand() as UserDefinedType;
        if (!(pat is IdPattern)) {
          ReportError(pat.Tok, "pattern doesn't correspond to a tuple");
          return;
        }

        IdPattern idpat = (IdPattern)pat;
        if (idpat.Arguments == null) {
          // simple variable
          idpat.CheckLinearVarPattern(udt, resolutionContext, resolver);
          return;
        }

        idpat.Ctor = tupleTypeDecl.GroundingCtor;

        //We expect the number of arguments in the type of the matchee and the provided pattern to match, except if the pattern is a bound variable
        if (udt.TypeArgs.Count != idpat.Arguments.Count) {
          if (idpat.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
            ReportError(pat.Tok,
              $"the case pattern is a {idpat.Arguments.Count}-element tuple, while the match expression is a {udt.TypeArgs.Count}-element tuple");
          } else {
            ReportError(pat.Tok,
              $"case pattern '{idpat.Id}' has {idpat.Arguments.Count} arguments whereas the match expression has {udt.TypeArgs.Count}");
          }
        }

        var pairTP = udt.TypeArgs.Zip(idpat.Arguments, (x, y) => new Tuple<Type, ExtendedPattern>(x, y));

        foreach (var tp in pairTP) {
          var t = resolver.PartiallyResolveTypeForMemberSelection(pat.Tok, tp.Item1).NormalizeExpand();
          tp.Item2.CheckLinearExtendedPattern(t, resolutionContext, resolver);
        }
        return;
      } else {
        // matching a datatype value
        if (!(pat is IdPattern)) {
          Contract.Assert(pat is LitPattern);
          ReportError(pat.Tok, "Constant pattern used in place of datatype");
          return;
        }
        IdPattern idpat = (IdPattern)pat;

        var dtd = sourcePreType.Decl as DatatypeDecl;
        Dictionary<string, DatatypeCtor> ctors = dtd.ConstructorsByName;
        if (ctors == null) {
          Contract.Assert(false);
          throw new cce.UnreachableException(); // Datatype not found
        }
        DatatypeCtor ctor = null;
        // Check if the head of the pattern is a constructor or a variable
        if (ctors.TryGetValue(idpat.Id, out ctor)) {
          /* =[3]= */
          idpat.Ctor = ctor;
          if (ctor != null && idpat.Arguments == null && ctor.Formals.Count == 0) {
            // nullary constructor without () -- so convert it to a constructor
            idpat.MakeAConstructor();
          }
          if (idpat.Arguments == null) {
            // pat is a variable
            return;
          } else if (ctor.Formals != null && ctor.Formals.Count == idpat.Arguments.Count) {
            if (ctor.Formals.Count == 0) {
              // if nullary constructor
              return;
            } else {
              // if non-nullary constructor
              var subst = TypeParameter.SubstitutionMap(dtd.TypeArgs, sourcePreType.NormalizeExpand().TypeArgs);
              var argTypes = ctor.Formals.ConvertAll<Type>(x => x.Type.Subst(subst));
              var pairFA = argTypes.Zip(idpat.Arguments, (x, y) => new Tuple<Type, ExtendedPattern>(x, y));
              foreach (var fa in pairFA) {
                // get DatatypeDecl of Formal, recursive call on argument
                fa.Item2.CheckLinearExtendedPattern(fa.Item1, resolutionContext, resolver);
              }
            }
          } else {
            // else applied to the wrong number of arguments
            ReportError(idpat.Tok, "constructor {0} of arity {2} is applied to {1} argument(s)", idpat.Id,
              (idpat.Arguments == null ? 0 : idpat.Arguments.Count), ctor.Formals.Count);
          }
        } else {
          /* =[4]= */
          // pattern is a variable OR error (handled in CheckLinearVarPattern)
          CheckLinearVarPattern(idpat, sourcePreType, resolutionContext);
        }
      }
#endif
    }

#if SOON
    public void CheckLinearVarPattern(IdPattern idPattern, DPreType sourcePreType, ResolutionContext resolutionContext) {
      if (idPattern.Arguments != null) {
        if (idPattern.Id == BuiltIns.TupleTypeCtorName(1)) {
          // TODO: this can be allowed if "sourcePreType" is the singleton (ghost) tuple type
          ReportError(idPattern.Tok, "parentheses are not allowed around a pattern");
        } else {
          ReportError(idPattern.Tok, $"member '{idPattern.Id}' does not exist in type '{sourcePreType}");
        }
        return;
      }

      if (idPattern.IsWildcardPattern) {
        // Wildcard. All is good.
        return;
      }
      if (scope.FindInCurrentScope(idPattern.Id) != null) {
        ReportError(idPattern.Tok, "Duplicate parameter name: {0}", idPattern.Id);
        return;
      }

      var e = new NameSegment(idPattern.Tok, idPattern.Id, null);
      resolver.ResolveNameSegment(e, true, null, resolutionContext, false, false);
      if (e.ResolvedExpression == null) {
        resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
      } else {
        // finds in full scope, not just current scope
        if (e.Resolved is MemberSelectExpr mse) {
          if (mse.Member.IsStatic && mse.Member is ConstantField cf) {
            Expression c = cf.Rhs;
            if (c is LiteralExpr lit) {
              this.ResolvedLit = lit;
              if (type.Equals(e.ResolvedExpression.Type)) {
                // OK - type is correct
              } else {
                // may well be a proxy so add a type constraint
                resolver.ConstrainSubtypeRelation(e.ResolvedExpression.Type, type, this.Tok,
                  "the type of the pattern ({0}) does not agree with the match expression ({1})", e.ResolvedExpression.Type, type);
              }
            } else {
              ReportError(this.Tok, "{0} is not initialized as a constant literal", this.Id);
              resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
            }
          } else {
            // Not a static const, so just a variable
            resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
          }
        } else {
          resolver.ScopePushAndReport(resolver.scope, new BoundVar(this.Tok, this.Id, type), "parameter");
        }
      }
    }
#endif

    private void ResolveMatchCaseStmt(NestedMatchCaseStmt kase, PreType sourcePreType, Dictionary<TypeParameter, PreType> typeSubstMap,
      ResolutionContext resolutionContext) {
#if SOON
      var beforeResolveErrorCount = ErrorCount;

      var boundVars = kase.Pat.ReplaceTypesWithBoundVariables(resolver, resolutionContext).ToList();
      foreach (var boundVar in boundVars) {
        var localVariable = new LocalVariable(boundVar.var.RangeToken, boundVar.var.Name, boundVar.var.Type, boundVar.var.IsGhost);
        var casePattern = new CasePattern<LocalVariable>(localVariable.RangeToken.EndToken, localVariable);
        var varDecl = new VarDeclPattern(localVariable.Tok.ToRange(), casePattern, boundVar.usage, false);
        kase.Body.Insert(0, varDecl);
      }

      Pat.Resolve(resolver, resolutionContext, sourcePreType, resolutionContext.IsGhost, true, false, false);
      if (ErrorCount == beforeResolveErrorCount) {
        dominatingStatementLabels.PushMarker();
        foreach (Statement ss in kase.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
        dominatingStatementLabels.PopMarker();
      }
#endif
    }
  }
}
