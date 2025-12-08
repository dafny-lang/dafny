//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using DafnyCore;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using ResolutionContext = Microsoft.Dafny.ResolutionContext;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {
    // ---------------------------------------- Expressions ----------------------------------------

    public void ResolveExpression(Expression expr, ResolutionContext resolutionContext) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

      if (expr.PreType != null) {
        // expression has already been pre-resolved
        return;
      }

      switch (expr) {
        case ParensExpression expression: {
            var e = expression;
            ResolveExpression(e.E, resolutionContext);
            var innerOrigin = e.E.Origin;
            e.ResolvedExpression = e.E; // Overwrites the range, which is not suitable for ParensExpressions
            e.E.SetOrigin(innerOrigin);
            e.PreType = e.E.PreType;
            break;
          }
        case ChainingExpression expression: {
            var e = expression;
            ResolveExpression(e.E, resolutionContext);
            e.ResolvedExpression = e.E;
            e.PreType = e.E.PreType;
            break;
          }
        case NegationExpression expression: {
            var e = expression;

            if (e.E is ApproximateExpr approxExpr) {
              var literalStr = "...";
              if (approxExpr.Expr is LiteralExpr { Value: BigDec dec }) {
                literalStr = dec.ToString();
              }
              resolver.ReportError(ResolutionErrors.ErrorId.r_approximate_prefix_after_negation, e.Origin,
                $"The approximate literal prefix ~ cannot be used after unary negation. " +
                $"Use ~-{literalStr} instead of -~{literalStr} to negate an approximate literal.");
            }

            ResolveExpression(e.E, resolutionContext);
            e.PreType = CreatePreTypeProxy("result of unary -");
            AddSubtypeConstraint(e.PreType, e.E.PreType, e.E.Origin,
              $"type of argument to unary - ({{1}}) must agree with the result type ({{0}})");
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.NumericOrBitvector, e.E.PreType, e.E.Origin, "type of unary - must be of a numeric or bitvector type (instead got {0})");
            // Note, e.ResolvedExpression will be filled in during CheckTypeInference, at which time e.PreType has been determined
            break;
          }
        case LiteralExpr literalExpr: {
            var e = literalExpr;

            if (e is StaticReceiverExpr eStatic) {
              resolver.ResolveType(eStatic.Origin, eStatic.UnresolvedType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
              eStatic.PreType = Type2PreType(eStatic.UnresolvedType, "static receiver type");
            } else {
              if (e.Value == null) {
                e.PreType = CreatePreTypeProxy("literal 'null'");
                Constraints.AddDefaultAdvice(e.PreType, CommonAdvice.Target.Object);
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IsNullableRefType, e.PreType, e.Origin, "type of 'null' is a reference type, but it is used as {0}");
              } else if (e.Value is BigInteger) {
                e.PreType = CreatePreTypeProxy($"integer literal '{e.Value}'");
                Constraints.AddDefaultAdvice(e.PreType, CommonAdvice.Target.Int);
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IntOrBitvectorOrORDINAL, e.PreType, e.Origin, "integer literal used as if it had type {0}");
              } else if (e.Value is BaseTypes.BigDec) {
                e.PreType = CreatePreTypeProxy($"decimal literal '{e.Value}'");
                // Add Real advice as default, but it can be overridden by equality constraints from fp64 contexts
                Constraints.AddDefaultAdvice(e.PreType, CommonAdvice.Target.Real);
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InRealFamily, e.PreType, e.Origin, "decimal literal used as if it had type {0}");
              } else if (e.Value is bool boolValue) {
                e.PreType = CreatePreTypeProxy($"boolean literal '{boolValue.ToString().ToLower()}'");
                Constraints.AddDefaultAdvice(e.PreType, CommonAdvice.Target.Bool);
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InBoolFamily, e.PreType, e.Origin, "boolean literal used as if it had type {0}");
              } else if (e is CharLiteralExpr charLiteralExpr) {
                e.PreType = CreatePreTypeProxy($"character literal '{e.EscapedValue}'");
                Constraints.AddDefaultAdvice(e.PreType, CommonAdvice.Target.Char);
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InCharFamily, e.PreType, e.Origin, "character literal used as if it had type {0}");
              } else if (e is StringLiteralExpr stringLiteralExpr) {
                var charPreType = CreatePreTypeProxy($"character in string literal");
                Constraints.AddDefaultAdvice(charPreType, CommonAdvice.Target.Char);
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InCharFamily, charPreType, e.Origin, "character literal used as if it had type {0}");
                ResolveCollectionProducingExpr(PreType.TypeNameSeq, $"string literal \"{e.EscapedValue}\"", e, charPreType, PreTypeConstraints.CommonConfirmationBag.InSeqFamily, true);
              } else {
                Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected literal type
              }
            }

            break;
          }
        case ThisExpr: {
            if (!scope.AllowInstance) {
              ReportError(expr, "'this' is not allowed in a 'static' context");
            }
            if (currentClass is DefaultClassDecl) {
              // there's no type
            } else if (currentClass == null) {
              Contract.Assert(resolver.reporter.HasErrors);
            } else {
              var ty = ModuleResolver.GetThisType(expr.Origin, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
              expr.PreType = Type2PreType(ty, "type of 'this'");
            }

            break;
          }
        case IdentifierExpr identifierExpr: {
            var e = identifierExpr;
            e.Var = scope.Find(e.Name);
            if (e.Var != null) {
              identifierExpr.PreType = e.Var.PreType;
            } else {
              ReportError(identifierExpr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
            }

            break;
          }
        case DatatypeValue value: {
            var dtv = value;
            TopLevelDecl decl = value.Ctor?.EnclosingDatatype;
            if (decl == null && !resolver.moduleInfo.TopLevels.TryGetValue(dtv.DatatypeName, out decl)) {
              ReportError(value.Origin, "Undeclared datatype: {0}", dtv.DatatypeName);
            } else if (decl is AmbiguousTopLevelDecl ad) {
              ReportError(value.Origin,
                "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)",
                dtv.DatatypeName, ad.ModuleNames());
            } else if (decl is DatatypeDecl dtd) {
              ResolveDatatypeValue(resolutionContext, dtv, dtd, null);
            } else {
              ReportError(value.Origin, "Expected datatype: {0}", dtv.DatatypeName);
            }

            break;
          }
        case DisplayExpression expression: {
            var e = expression;
            var elementPreType = CreatePreTypeProxy("display expression element type");
            foreach (var ee in e.Elements) {
              ResolveExpression(ee, resolutionContext);
              AddSubtypeConstraint(elementPreType, ee.PreType, ee.Origin,
                "All elements of display must have some common supertype (got {1}, but needed type or type of previous elements is {0})");
            }
            if (expression is SetDisplayExpr setDisplayExpr) {
              var confirmationFamily = setDisplayExpr.Finite
                ? PreTypeConstraints.CommonConfirmationBag.InSetFamily
                : PreTypeConstraints.CommonConfirmationBag.InIsetFamily;
              ResolveCollectionProducingExpr(PreType.SetTypeName(setDisplayExpr.Finite), "display", setDisplayExpr, elementPreType, confirmationFamily);
            } else if (expression is MultiSetDisplayExpr multiSetDisplayExpr) {
              ResolveCollectionProducingExpr(PreType.TypeNameMultiset, "display", e, elementPreType,
                PreTypeConstraints.CommonConfirmationBag.InMultisetFamily);
            } else {
              ResolveCollectionProducingExpr(PreType.TypeNameSeq, "display", e, elementPreType, PreTypeConstraints.CommonConfirmationBag.InSeqFamily);
            }

            break;
          }
        case MapDisplayExpr displayExpr: {
            var e = displayExpr;
            var domainPreType = CreatePreTypeProxy("map display expression domain type");
            var rangePreType = CreatePreTypeProxy("map display expression range type");
            foreach (MapDisplayEntry p in e.Elements) {
              ResolveExpression(p.A, resolutionContext);
              AddSubtypeConstraint(domainPreType, p.A.PreType, p.A.Origin,
                "All elements of display must have some common supertype (got {1}, but needed type or type of previous elements is {0})");
              ResolveExpression(p.B, resolutionContext);
              AddSubtypeConstraint(rangePreType, p.B.PreType, p.B.Origin,
                "All elements of display must have some common supertype (got {1}, but needed type or type of previous elements is {0})");
            }

            ResolveMapProducingExpr(e.Finite, "display", displayExpr, domainPreType, rangePreType);
            break;
          }
        case NameSegment segment: {
            var e = segment;
            ResolveNameSegment(e, true, null, resolutionContext, false);

            if (e.PreType is PreTypePlaceholderModule) {
              ReportError(e.Origin, "name of module ({0}) is used as a variable", e.Name);
              ResetTypeAssignment(e); // the rest of type checking assumes actual types
            } else if (e.PreType is PreTypePlaceholderType) {
              ReportError(e.Origin, "name of type ({0}) is used as a variable", e.Name);
              ResetTypeAssignment(e); // the rest of type checking assumes actual types
            }

            break;
          }
        case ExprDotName name: {
            var e = name;
            ResolveDotSuffix(e, false, true, null, resolutionContext, false);
            if (e.PreType is PreTypePlaceholderModule) {
              ReportError(e.Origin, "name of module ({0}) is used as a variable", e.SuffixName);
              ResetTypeAssignment(e);  // the rest of type checking assumes actual types
            } else if (e.PreType is PreTypePlaceholderType) {
              ReportError(e.Origin, "name of type ({0}) is used as a variable", e.SuffixName);
              ResetTypeAssignment(e);  // the rest of type checking assumes actual types
            }

            break;
          }
        case ApplySuffix applySuffix:
          ResolveApplySuffix(applySuffix, resolutionContext, false);
          break;
        case MemberSelectExpr selectExpr: {
            var e = selectExpr;
            if (e.WasResolved()) {
              // Already resolved, nothing to do
              break;
            }
            Contract.Assert(false); // this case is always handled by ResolveExprDotCall
            break;
          }
        case SeqSelectExpr selectExpr: {
            var e = selectExpr;

            ResolveExpression(e.Seq, resolutionContext);
            if (e.E0 != null) {
              ResolveExpression(e.E0, resolutionContext);
            }
            if (e.E1 != null) {
              ResolveExpression(e.E1, resolutionContext);
            }

            if (e.SelectOne) {
              Contract.Assert(e.E0 != null);
              Contract.Assert(e.E1 == null);
              e.PreType = ResolveSingleSelectionExpr(e.Origin, e.Seq.PreType, e.E0);
            } else {
              ResolveRangeSelectionExpr(e.Origin, e.Seq.PreType, e, e.E0, e.E1);
            }

            break;
          }
        case MultiSelectExpr selectExpr: {
            var e = selectExpr;

            ResolveExpression(e.Array, resolutionContext);
            var elementPreType = CreatePreTypeProxy("multi-dim array select");
            var arrayPreType = BuiltInArrayType(e.Indices.Count, elementPreType);
            AddSubtypeConstraint(arrayPreType, e.Array.PreType, e.Array.Origin, "array selection requires an {0} (got {1})");
            int i = 0;
            foreach (var indexExpression in e.Indices) {
              ResolveExpression(indexExpression, resolutionContext);
              ConstrainToIntFamilyOrBitvector(indexExpression.PreType, indexExpression.Origin,
                "array selection requires integer- or bitvector-based numeric indices (got {0} for index " + i + ")");
              i++;
            }
            e.PreType = elementPreType;
            break;
          }
        case SeqUpdateExpr updateExpr: {
            var e = updateExpr;
            ResolveExpression(e.Seq, resolutionContext);
            ResolveExpression(e.Index, resolutionContext);
            ResolveExpression(e.Value, resolutionContext);
            Constraints.AddGuardedConstraint(() => {
              var ancestorPreType = e.Seq.PreType.NormalizeWrtScope() is not DPreType sourcePreType ? null : AncestorPreType(sourcePreType);
              var familyDeclName = ancestorPreType?.Decl.Name;
              if (familyDeclName == PreType.TypeNameSeq) {
                var elementPreType = ancestorPreType.Arguments[0];
                ConstrainToIntFamilyOrBitvector(e.Index.PreType, e.Index.Origin, "sequence update requires integer- or bitvector-based index (got {1})");
                AddSubtypeConstraint(elementPreType, e.Value.PreType, e.Value.Origin,
                  "sequence update requires the value to have the element type of the sequence (got {1})");
                return true;
              } else if (familyDeclName is PreType.TypeNameMap or PreType.TypeNameImap) {
                var domainPreType = ancestorPreType.Arguments[0];
                var rangePreType = ancestorPreType.Arguments[1];
                AddSubtypeConstraint(domainPreType, e.Index.PreType, e.Index.Origin,
                  familyDeclName + " update requires domain element to be of type {0} (got {1})");
                AddSubtypeConstraint(rangePreType, e.Value.PreType, e.Value.Origin,
                  familyDeclName + " update requires the value to have the range type {0} (got {1})");
                return true;
              } else if (familyDeclName == PreType.TypeNameMultiset) {
                var elementPreType = ancestorPreType.Arguments[0];
                AddSubtypeConstraint(elementPreType, e.Index.PreType, e.Index.Origin,
                  "multiset update requires domain element to be of type {0} (got {1})");
                ConstrainToIntFamily(e.Value.PreType, e.Value.Origin, "multiset update requires integer-based numeric value (got {0})");
                return true;
              } else if (familyDeclName != null) {
                ReportError(expr.Origin, "update requires a sequence, map, or multiset (got {0})", e.Seq.PreType);
                return true;
              }
              return false;
            });

            updateExpr.PreType = CreatePreTypeProxy("result of _[_:=_]");
            AddSubtypeConstraint(updateExpr.PreType, e.Seq.PreType, e.Origin,
              $"result of update expression must agree with the source type ({{0}})");
            break;
          }
        case DatatypeUpdateExpr datatypeUpdateExpr: {
            var e = datatypeUpdateExpr;
            // Resolve the root and all the updated-value expressions, since these may require lookups in the current local-variable scope
            ResolveExpression(e.Root, resolutionContext);
            datatypeUpdateExpr.PreType = CreatePreTypeProxy("datatype update");
            foreach (var (_, _, updateExpr) in e.Updates) {
              ResolveExpression(updateExpr, resolutionContext);
            }
            //e.ResolvedExpression = e;
            // Next, at a leisurely pace (that is, waiting until enough of the pre-type of .Root is known), resolve the update expression
            // and desugar it into some kind of nested let expression.
            Constraints.AddGuardedConstraint(() => {
              if (e.Root.PreType.NormalizeWrtScope() is DPreType tentativeRootPreType) {
                if (tentativeRootPreType.Decl is DatatypeDecl datatypeDecl) {
                  var (ghostLet, compiledLet) = ResolveDatatypeUpdate(expr.Origin, tentativeRootPreType, e.Root, datatypeDecl, e.Updates,
                    resolutionContext, out var members, out var legalSourceConstructors);
                  // if 'let' returns as 'null', an error has already been reported
                  if (ghostLet != null) {
                    e.ResolvedExpression = ghostLet;
                    e.ResolvedCompiledExpression = compiledLet;
                    e.Members = members;
                    e.LegalSourceConstructors = legalSourceConstructors;
                    Constraints.AddEqualityConstraint(expr.PreType, ghostLet.PreType, expr.Origin,
                      "result of datatype update expression of type '{1}' is used as if it were of type '{0}'");
                    if (ghostLet != compiledLet) {
                      Constraints.AddEqualityConstraint(expr.PreType, compiledLet.PreType, expr.Origin,
                        "result of datatype update expression of type '{1}' is used as if it were of type '{0}'");
                    }
                  }
                } else {
                  ReportError(expr, "datatype update expression requires a root expression of a datatype (got {0})", tentativeRootPreType);
                }
                return true;
              }
              return false;
            });
            break;
          }
        case FunctionCallExpr:
          Contract.Assert(false); // this case is always handled by ResolveExprDotCall
          break;
        case ApplyExpr applyExpr: {
            var e = applyExpr;
            ResolveExpression(e.Function, resolutionContext);
            foreach (var arg in e.Args) {
              ResolveExpression(arg, resolutionContext);
            }
            applyExpr.PreType = CreatePreTypeProxy("apply expression result");

            Constraints.AddGuardedConstraint(() => {
              if (e.Function.PreType.NormalizeWrtScope() is DPreType dp) {
                if (!DPreType.IsArrowType(dp.Decl)) {
                  ReportError(e.Origin, "non-function expression (of type {0}) is called with parameters", e.Function.PreType);
                } else {
                  var arity = dp.Decl.TypeArgs.Count - 1;
                  if (arity != e.Args.Count) {
                    ReportError(e.Origin,
                      "wrong number of arguments to function application (function type '{0}' expects {1}, got {2})", e.Function.PreType,
                      arity, e.Args.Count);
                  } else {
                    for (var i = 0; i < arity; i++) {
                      AddSubtypeConstraint(dp.Arguments[i], e.Args[i].PreType, e.Args[i].Origin,
                        "type mismatch for argument" + (arity == 1 ? "" : " " + i) + " (function expects {0}, got {1})");
                    }
                    AddSubtypeConstraint(expr.PreType, dp.Arguments[arity], expr.Origin, "function result '{1}' used as if it had type '{0}'");
                  }
                }
                return true;
              }
              return false;
            });
            break;
          }
        case SeqConstructionExpr constructionExpr: {
            var e = constructionExpr;
            var elementType = e.ExplicitElementType ?? new InferredTypeProxy();
            resolver.ResolveType(e.Origin, elementType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            var elementPreType = Type2PreType(elementType);
            ResolveExpression(e.N, resolutionContext);
            ConstrainToIntFamily(e.N.PreType, e.N.Origin, "sequence construction must use an integer-based expression for the sequence size (got {0})");
            ResolveExpression(e.Initializer, resolutionContext);
            var intPreType = Type2PreType(resolver.SystemModuleManager.Nat());
            var arrowPreType = new DPreType(BuiltInArrowTypeDecl(1), [intPreType, elementPreType]);
            Constraints.AddSubtypeConstraint(arrowPreType, e.Initializer.PreType, e.Initializer.Origin,
              () => {
                var strFormat = "sequence-construction initializer expression expected to have type '{0}' (instead got '{1}')";
                if (PreType.Same(elementPreType, e.Initializer.PreType)) {
                  var hintString = " (perhaps write '_ =>' in front of the expression you gave in order to make it an arrow type)";
                  strFormat += hintString;
                }
                return strFormat;
              });
            ResolveCollectionProducingExpr(PreType.TypeNameSeq, "constructor", constructionExpr, elementPreType, PreTypeConstraints.CommonConfirmationBag.InSeqFamily);
            break;
          }
        case MultiSetFormingExpr formingExpr: {
            var e = formingExpr;
            ResolveExpression(e.E, resolutionContext);
            var targetElementPreType = CreatePreTypeProxy("multiset conversion element type");
            Constraints.AddGuardedConstraint(() => {
              if (e.E.PreType.NormalizeWrtScope() is DPreType dp) {
                var familyDeclName = AncestorName(dp);
                if (familyDeclName is PreType.TypeNameSet or PreType.TypeNameSeq && AncestorPreType(dp) is { } ancestorPreType) {
                  Contract.Assert(ancestorPreType.Arguments.Count == 1);
                  var sourceElementPreType = ancestorPreType.Arguments[0];
                  AddSubtypeConstraint(targetElementPreType, sourceElementPreType, e.E.Origin, "expecting element type {0} (got {1})");
                } else {
                  ReportError(e.E.Origin, "can only form a multiset from a seq or set (got {0})", e.E.PreType);
                }
                return true;
              }
              return false;
            });
            ResolveCollectionProducingExpr(PreType.TypeNameMultiset, "conversion", formingExpr, targetElementPreType,
              PreTypeConstraints.CommonConfirmationBag.InMultisetFamily);
            break;
          }
        case OldExpr oldExpr: {
            var e = oldExpr;
            e.AtLabel = ResolveDominatingLabelInExpr(oldExpr.Origin, e.At, "old", resolutionContext);
            ResolveExpression(e.Expr, new ResolutionContext(resolutionContext.CodeContext, false) with { InOld = true });
            oldExpr.PreType = e.Expr.PreType;
            break;
          }
        case UnchangedExpr unchangedExpr: {
            var e = unchangedExpr;
            e.AtLabel = ResolveDominatingLabelInExpr(unchangedExpr.Origin, e.At, "unchanged", resolutionContext);
            foreach (var fe in e.Frame) {
              ResolveFrameExpression(fe, FrameExpressionUse.Unchanged, resolutionContext.CodeContext);
            }
            ConstrainTypeExprBool(e, "result of 'unchanged' is boolean, but is used as if it had type {0}");
            break;
          }
        case FreshExpr freshExpr: {
            var e = freshExpr;
            ResolveExpression(e.E, resolutionContext);
            e.AtLabel = ResolveDominatingLabelInExpr(freshExpr.Origin, e.At, "fresh", resolutionContext);
            // the type of e.E must be either an object or a set/seq of objects
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.Freshable, e.E.PreType, e.E.Origin, "the argument of a fresh expression must denote an object or a set or sequence of objects (instead got {0})");
            ConstrainTypeExprBool(e, "result of 'fresh' is boolean, but is used as if it had type {0}");
            break;
          }
        case UnaryOpExpr opExpr: {
            var e = opExpr;
            ResolveExpression(e.E, resolutionContext);
            switch (e.Op) {
              case UnaryOpExpr.Opcode.Not:
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.BooleanBits, e.E.PreType, opExpr.Origin, "logical/bitwise negation expects a boolean or bitvector argument (instead got {0})");
                opExpr.PreType = e.E.PreType;
                Constraints.AddDefaultAdvice(e.PreType, CommonAdvice.Target.Bool);
                break;
              case UnaryOpExpr.Opcode.Cardinality:
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.Sizeable, e.E.PreType, opExpr.Origin, "size operator expects a collection argument (instead got {0})");
                opExpr.PreType = CreatePreTypeProxy("cardinality");
                ConstrainToIntFamily(opExpr.PreType, opExpr.Origin, "integer literal used as if it had type {0}");
                break;
              case UnaryOpExpr.Opcode.Allocated:
                // the argument is allowed to have any type at all
                opExpr.PreType = ConstrainResultToBoolFamily(opExpr.Origin, "allocated", "boolean literal used as if it had type {0}");
                if ((resolutionContext.CodeContext is Function && !resolutionContext.InOld) ||
                    resolutionContext.CodeContext is ConstantField ||
                    CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl) {
                  var declKind = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl redir
                    ? redir.WhatKind
                    : ((MemberDecl)resolutionContext.CodeContext).WhatKind;
                  ReportError(opExpr, "a {0} definition is not allowed to depend on the set of allocated references", declKind);
                }
                break;
              case UnaryOpExpr.Opcode.Assigned:
                // the argument is allowed to have any type at all
                expr.PreType = ConstrainResultToBoolFamily(expr.Origin, "assigned", "boolean literal used as if it had type {0}");
                break;
              default:
                Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected unary operator
            }

            break;
          }
        case ApproximateExpr approximateExpr: {
            var e = approximateExpr;
            ResolveExpression(e.Expr, resolutionContext);

            // Check that there's no space between ~ and the literal
            var tildePos = e.Origin.EntireRange.StartToken;
            var literalPos = e.Expr.Origin.EntireRange.StartToken;
            if (tildePos.line == literalPos.line && literalPos.col - tildePos.col > 1) {
              ReportError(e, "~ prefix must immediately precede the literal with no intervening space");
            }

            var innerExpr = e.Expr;

            if (innerExpr is NegationExpression neg) {
              innerExpr = neg.E;
            }

            if (innerExpr is LiteralExpr lit) {
              if (lit.Value is BigDec decValue) {
                // Create a proxy that can be constrained to fp32 or fp64
                var floatProxy = CreatePreTypeProxy("approximate literal");

                // Don't add default advice - let context (e.g., 'as fp32') determine the type
                // Fallback to fp64 is applied later for unresolved proxies

                // Add confirmation that it must be fp32 or fp64 (not real)
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InFloatFamily, floatProxy, e.Origin, "approximate literal used as if it had type {0}");

                e.PreType = floatProxy;
                e.ResolvedExpression = e.Expr;
                e.Expr.PreType = floatProxy;
                lit.PreType = floatProxy;

                if (lit is DecimalLiteralExpr decLit) {
                  decLit.IsApproximate = true;
                }
                if (e.Expr is DecimalLiteralExpr exprDecLit && exprDecLit != lit) {
                  exprDecLit.IsApproximate = true;
                }

              } else if (lit.Value is BigInteger) {
                ReportError(e, "~ prefix not allowed on integer literals");
                e.PreType = new DPreType(BuiltInTypeDecl(PreType.TypeNameInt), []);
              } else if (lit.Value is bool) {
                ReportError(e, "~ prefix not allowed on boolean literals");
                e.PreType = new DPreType(BuiltInTypeDecl(PreType.TypeNameBool), []);
              } else if (lit is CharLiteralExpr) {
                ReportError(e, "~ prefix not allowed on character literals");
                e.PreType = new DPreType(BuiltInTypeDecl(PreType.TypeNameChar), []);
              } else if (lit is StringLiteralExpr) {
                ReportError(e, "~ prefix not allowed on string literals");
                e.PreType = new DPreType(BuiltInTypeDecl(PreType.TypeNameString), []);
              } else {
                ReportError(e, "~ prefix can only be applied to numeric literals");
                e.PreType = CreatePreTypeProxy("error");
              }
            } else {
              ReportError(e, "~ prefix can only be applied to numeric literals, not to variables or expressions");
              e.PreType = e.Expr.PreType;
            }

            e.ResolvedExpression ??= e.Expr;
            break;
          }
        case ConversionExpr conversionExpr: {
            var e = conversionExpr;
            ResolveExpression(e.E, resolutionContext);
            var prevErrorCount = ErrorCount;
            resolver.ResolveType(e.Origin, e.ToType, resolutionContext, new ModuleResolver.ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
            if (ErrorCount == prevErrorCount) {
              var toPreType = Type2PreType(e.ToType);
              var errorMessage = () => {
                string errorMessageFormat;
                if (toPreType.Normalize() is DPreType dtoPreType && AncestorPreType(dtoPreType)?.Decl is { } ancestorDecl) {
                  var familyDeclName = ancestorDecl.Name;
                  if (familyDeclName == PreType.TypeNameInt) {
                    errorMessageFormat = "type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {1})";
                  } else if (familyDeclName == PreType.TypeNameReal) {
                    var legacy = !resolver.Options.Get(CommonOptionBag.GeneralNewtypes);
                    if (legacy) {
                      errorMessageFormat = "type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {1})";
                    } else if (dtoPreType.Decl.Name == PreType.TypeNameReal) {
                      errorMessageFormat = "type conversion to real is allowed only from numeric-based types (got {1})";
                    } else {
                      errorMessageFormat = "type conversion to a real-based type is allowed only from real (got {1})";
                    }
                  } else if (familyDeclName is PreType.TypeNameFp32 or PreType.TypeNameFp64) {
                    errorMessageFormat = $"type conversion to {familyDeclName} is allowed only from numeric types (int, real, fp32, fp64) (got {{1}})";
                  } else if (IsBitvectorName(familyDeclName)) {
                    errorMessageFormat = "type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {1})";
                  } else if (familyDeclName == PreType.TypeNameChar) {
                    errorMessageFormat = "type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got {1})";
                  } else if (familyDeclName == PreType.TypeNameORDINAL) {
                    errorMessageFormat = "type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got {1})";
                  } else if (DPreType.IsReferenceTypeDecl(ancestorDecl)) {
                    errorMessageFormat = "type cast to reference type '{0}' must be from an expression of a compatible type (got '{1}')";
                  } else if (ancestorDecl is TraitDecl) {
                    errorMessageFormat = "type cast to trait type '{0}' must be from an expression of a compatible type (got '{1}')";
                  } else {
                    errorMessageFormat = "type cast to type '{0}' must be from an expression of a compatible type (got '{1}')";
                  }
                } else {
                  errorMessageFormat = "type conversion target type not determined (got '{0}')";
                }
                return string.Format(errorMessageFormat, toPreType, e.E.PreType);
              };

              // For approximate literals with fp32/fp64 target, use equality to infer the target type
              if (toPreType.Normalize() is DPreType dtoPreType2 &&
                  (dtoPreType2.Decl.Name == PreType.TypeNameFp32 || dtoPreType2.Decl.Name == PreType.TypeNameFp64) &&
                  e.E is ConcreteSyntaxExpression { ResolvedExpression: DecimalLiteralExpr { IsApproximate: true } }) {
                Constraints.AddEqualityConstraint(toPreType, e.E.PreType, expr.Origin, errorMessage());
                Constraints.AddDefaultAdvice(e.E.PreType, dtoPreType2.Decl.Name == PreType.TypeNameFp32 ? CommonAdvice.Target.Fp32 : CommonAdvice.Target.Fp64);
              } else {
                AddComparableConstraint(toPreType, e.E.PreType, expr.Origin, true, errorMessage);
              }
              e.PreType = toPreType;
            } else {
              e.PreType = CreatePreTypeProxy("'as' target type");
            }

            break;
          }
        case TypeTestExpr testExpr: {
            var e = testExpr;
            ResolveExpression(e.E, resolutionContext);
            testExpr.PreType = ConstrainResultToBoolFamilyOperator(testExpr.Origin, "is");
            resolver.ResolveType(e.Origin, e.ToType, resolutionContext, new ModuleResolver.ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
            var toPreType = Type2PreType(e.ToType);
            AddComparableConstraint(toPreType, e.E.PreType, testExpr.Origin, true,
              "type test for type '{0}' must be from an expression assignable to it (got '{1}')");
            break;
          }
        case BinaryExpr binaryExpr: {
            var e = binaryExpr;
            ResolveExpression(e.E0, resolutionContext);
            ResolveExpression(e.E1, resolutionContext);
            binaryExpr.PreType = ResolveBinaryExpr(e.Origin, e.Op, e.E0, e.E1, resolutionContext);
            break;
          }
        case TernaryExpr ternaryExpr: {
            var e = ternaryExpr;
            ResolveExpression(e.E0, resolutionContext);
            ResolveExpression(e.E1, resolutionContext);
            ResolveExpression(e.E2, resolutionContext);
            switch (e.Op) {
              case TernaryExpr.Opcode.PrefixEqOp:
              case TernaryExpr.Opcode.PrefixNeqOp:
                ternaryExpr.PreType = ConstrainResultToBoolFamily(ternaryExpr.Origin, "ternary op", "boolean literal used as if it had type {0}");
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IntOrORDINAL, e.E0.PreType, ternaryExpr.Origin, "prefix-equality limit argument must be an ORDINAL or integer expression (got {0})");
                AddComparableConstraint(e.E1.PreType, e.E2.PreType, ternaryExpr.Origin, false,
                  "arguments must have the same type (got {0} and {1})");
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IsCoDatatype, e.E1.PreType, ternaryExpr.Origin, "arguments to prefix equality must be codatatypes (instead of {0})");
                break;
              default:
                Contract.Assert(false);  // unexpected ternary operator
                break;
            }

            break;
          }
        case LetExpr letExpr: {
            var e = letExpr;
            if (e.Exact) {
              foreach (var bv in e.BoundVars) {
                int prevErrorCount = ErrorCount;
                resolver.ResolveType(bv.Origin, bv.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
                bv.PreType = Type2PreType(bv.Type);
              }
              foreach (var rhs in e.RHSs) {
                ResolveExpression(rhs, resolutionContext);
              }
              scope.PushMarker();
              if (e.LHSs.Count != e.RHSs.Count) {
                ReportError(letExpr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
              }
              var i = 0;
              foreach (var lhs in e.LHSs) {
                var rhsPreType = i < e.RHSs.Count ? e.RHSs[i].PreType : CreatePreTypeProxy("let RHS");
                ResolveCasePattern(lhs, rhsPreType, resolutionContext);
                // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
                var c = 0;
                foreach (var v in lhs.Vars) {
                  ScopePushAndReport(v, "let-variable", false); // .PreType's already assigned by ResolveCasePattern
                  c++;
                }
                if (c == 0) {
                  // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
                  ReportError(lhs.Origin, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
                }
                i++;
              }
            } else {
              // let-such-that expression
              if (e.RHSs.Count != 1) {
                ReportError(letExpr, "let-such-that expression must have just one RHS (found {0})", e.RHSs.Count);
              }
              // the bound variables are in scope in the RHS of a let-such-that expression
              scope.PushMarker();
              foreach (var lhs in e.LHSs) {
                Contract.Assert(lhs.Var != null);  // the parser already checked that every LHS is a BoundVar, not a general pattern
                var v = lhs.Var;
                resolver.ResolveType(v.Origin, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
                v.PreType = Type2PreType(v.Type);
                ScopePushAndReport(v, "let-variable", false);
                lhs.AssembleExprPreType(null);
              }
              foreach (var rhs in e.RHSs) {
                ResolveExpression(rhs, resolutionContext);
                ConstrainExpressionToBoolFamily(rhs, "type of RHS of let-such-that expression must be boolean (got {0})");
              }
            }
            ResolveExpression(e.Body, resolutionContext);
            ResolveAttributes(e, resolutionContext, false);
            scope.PopMarker();
            letExpr.PreType = e.Body.PreType;
            break;
          }
        case LetOrFailExpr failExpr: {
            var e = failExpr;
            e.ResolvedExpression = DesugarElephantExpr(e, resolutionContext);
            ResolveExpression(e.ResolvedExpression, resolutionContext);
            e.PreType = e.ResolvedExpression.PreType;
            Constraints.AddGuardedConstraint(() => {
              if (e.Rhs.PreType.NormalizeWrtScope() is DPreType receiverPreType) {
                bool expectExtract = e.Lhs != null;
                EnsureSupportsErrorHandling(e.Origin, receiverPreType, expectExtract, resolutionContext, null);
                return true;
              }
              return false;
            });
            break;
          }
        case QuantifierExpr quantifierExpr: {
            var e = quantifierExpr;
            if (resolutionContext.CodeContext is Function enclosingFunction) {
              enclosingFunction.ContainsQuantifier = true;
            }
            Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
            scope.PushMarker();
            foreach (var v in e.BoundVars) {
              resolver.ResolveType(v.Origin, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
              ScopePushAndReport(v, "bound-variable", true);
            }
            if (e.Range != null) {
              ResolveExpression(e.Range, resolutionContext);
              ConstrainTypeExprBool(e.Range, "range of quantifier must be of type bool (instead got {0})");
            }
            ResolveExpression(e.Term, resolutionContext);
            ConstrainTypeExprBool(e.Term, "body of quantifier must be of type bool (instead got {0})");
            // Since the body is more likely to infer the types of the bound variables, resolve it
            // first (above) and only then resolve the attributes (below).
            ResolveAttributes(e, resolutionContext, false);
            scope.PopMarker();
            quantifierExpr.PreType = ConstrainResultToBoolFamilyOperator(quantifierExpr.Origin, e.WhatKind);
            break;
          }
        case SetComprehension comprehension: {
            var e = comprehension;
            scope.PushMarker();
            foreach (var v in e.BoundVars) {
              resolver.ResolveType(v.Origin, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
              ScopePushAndReport(v, "bound-variable", true);
            }
            ResolveExpression(e.Range, resolutionContext);
            ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
            ResolveExpression(e.Term, resolutionContext);

            ResolveAttributes(e, resolutionContext, false);
            scope.PopMarker();

            ResolveCollectionProducingExpr(PreType.SetTypeName(e.Finite), "comprehension", comprehension, e.Term.PreType,
              e.Finite ? PreTypeConstraints.CommonConfirmationBag.InSetFamily : PreTypeConstraints.CommonConfirmationBag.InIsetFamily);
            break;
          }
        case MapComprehension comprehension: {
            var e = comprehension;
            scope.PushMarker();
            Contract.Assert(e.BoundVars.Count == 1 || (1 < e.BoundVars.Count && e.TermLeft != null));
            foreach (BoundVar v in e.BoundVars) {
              resolver.ResolveType(v.Origin, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
              ScopePushAndReport(v, "bound-variable", true);
            }
            ResolveExpression(e.Range, resolutionContext);
            ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
            if (e.TermLeft != null) {
              ResolveExpression(e.TermLeft, resolutionContext);
            }
            ResolveExpression(e.Term, resolutionContext);

            ResolveAttributes(e, resolutionContext, false);
            scope.PopMarker();

            ResolveMapProducingExpr(e.Finite, "comprehension", comprehension, e.TermLeft?.PreType ?? e.BoundVars[0].PreType, e.Term.PreType);
            break;
          }
        case LambdaExpr lambdaExpr: {
            var e = lambdaExpr;
            scope.PushMarker();
            foreach (var v in e.BoundVars) {
              resolver.ResolveType(v.Origin, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
              ScopePushAndReport(v, "bound-variable", true);
            }

            if (e.Range != null) {
              ResolveExpression(e.Range, resolutionContext);
              ConstrainTypeExprBool(e.Range, "precondition must be boolean (got {0})");
            }
            foreach (var read in e.Reads.Expressions) {
              ResolveFrameExpression(read, FrameExpressionUse.Reads, resolutionContext.CodeContext);
            }
            ResolveExpression(e.Term, resolutionContext);
            scope.PopMarker();
            lambdaExpr.PreType = BuiltInArrowType(e.BoundVars.ConvertAll(v => v.PreType), e.Body.PreType, e.Reads.Expressions.Count != 0, e.Range != null);
            break;
          }
        case WildcardExpr: {
            var obj = new DPreType(BuiltInTypeDecl(PreType.TypeNameObjectQ), []);
            expr.PreType = new DPreType(BuiltInTypeDecl(PreType.TypeNameSet), [obj]);
            break;
          }
        case StmtExpr stmtExpr: {
            var e = stmtExpr;
            int prevErrorCount = ErrorCount;
            ResolveStatement(e.S, resolutionContext);
            if (ErrorCount == prevErrorCount) {
              if (e.S is AssignStatement updateStmt && updateStmt.ResolvedStatements.Count == 1) {
                var call = (CallStmt)updateStmt.ResolvedStatements[0];
                if (call.Method is TwoStateLemma && !resolutionContext.IsTwoState) {
                  ReportError(call, "two-state lemmas can only be used in two-state contexts");
                }
              }
            }
            ResolveExpression(e.E, resolutionContext);
            stmtExpr.PreType = e.E.PreType;
            break;
          }
        case ITEExpr iteExpr: {
            var e = iteExpr;
            ResolveExpression(e.Test, resolutionContext);
            ResolveExpression(e.Thn, resolutionContext);
            ResolveExpression(e.Els, resolutionContext);
            ConstrainExpressionToBoolFamily(e.Test, "guard condition in if-then-else expression must be a boolean (instead got {0})");
            iteExpr.PreType = CreatePreTypeProxy("if-then-else branches");
            AddSubtypeConstraint(iteExpr.PreType, e.Thn.PreType, iteExpr.Origin, "the two branches of an if-then-else expression must have the same type (got {0} and {1})");
            AddSubtypeConstraint(iteExpr.PreType, e.Els.PreType, iteExpr.Origin, "the two branches of an if-then-else expression must have the same type (got {0} and {1})");
            break;
          }
        case DecreasesToExpr decreasesToExpr: {
            foreach (var e in decreasesToExpr.SubExpressions) {
              ResolveExpression(e, resolutionContext);
            }

            decreasesToExpr.PreType = ConstrainResultToBoolFamilyOperator(decreasesToExpr.Origin, "decreasesto");
            break;
          }

        case FieldLocationExpression fieldLocation: {
            void ResolveWith(Field resolvedField, Expression resolved1) {
              fieldLocation.ResolvedField = resolvedField;
              ResolveExpression(resolved1, resolutionContext);
              fieldLocation.ResolvedExpression = resolved1;
              fieldLocation.PreType = resolved1.PreType;
            }
            var name = fieldLocation.Name;
            MethodOrConstructor innerCallEnclosingMethod = null;
            if (fieldLocation.Lhs is NameSegment nameSegment && currentClass != null &&
                resolver.GetClassMembers(currentClass) is { } members &&
                members.TryGetValue(nameSegment.Name, out var member)) {
              if (EnclosingMethodCall == member) {
                innerCallEnclosingMethod = EnclosingMethodCall;
              } else if (EnclosingMethodCall != null) {
                ReportError(fieldLocation.Lhs, "Expected 'locals' or the explicit name of the enclosing method call '{0}' as the left-hand-side of the memory location expression, got '{1}'", EnclosingMethodCall.Name, nameSegment.Name);
                fieldLocation.PreType = CreatePreTypeProxy("field-location");
                return;
              } else {
                ReportError(fieldLocation.Lhs, "Expected 'locals', got unrelated method name '{0}'", nameSegment.Name);
                fieldLocation.PreType = CreatePreTypeProxy("field-location");
                return;
              }
              nameSegment.PreType = CreatePreTypeProxy(); // Never used, just in case.
            } else {
              ResolveExpression(fieldLocation.Lhs, resolutionContext);
            }

            Expression resolved;
            Field localField;

            if (innerCallEnclosingMethod != null) {
              var formal = EnclosingInputParameterFormals.Find(name.Value);
              if (formal == null) {
                // Let's give an hint about declared input parameters
                var hints = new List<string>();
                hints.AddRange(EnclosingInputParameterFormals.Names
                  .Where(n => n != null).Select(n => $"{EnclosingMethodCall!.Name}`{n}"));
                hints.AddRange(Scope.Names
                  .Where(n => n != null).Select(n => $"locals`{n}"));
                ReportError(fieldLocation, "input parameter '{0}' is not declared{1}", name, DidYouMeanOneOf(hints));
                fieldLocation.PreType = CreatePreTypeProxy("field-location");
                return;
              }

              localField = formal.GetLocalField(innerCallEnclosingMethod);
              var locals = new LocalsObjectExpression(fieldLocation.Lhs.Origin);
              ResolveExpression(locals, resolutionContext);
              resolved = CreateObjectFieldLocation(fieldLocation.Origin, locals, fieldLocation.Name, localField, true);
              ResolveWith(localField, resolved);
              return;
            }
            if (fieldLocation.Lhs is LocalsObjectExpression) {
              if (resolutionContext.AsMethod is not { } method) {
                ReportError(fieldLocation, "field location expressions cannot be used outside of a method");
                fieldLocation.PreType = CreatePreTypeProxy("field-location");
                return;
              }
              // We resolve the field as a local variable like for identifiers and name segments
              var v = scope.Find(name.Value);
              if (v == null) {
                var f = EnclosingInputParameterFormals.Find(name.Value);
                var hint = "";
                if (f != null) {
                  hint = DidYouMeanOneOf([$"{EnclosingMethodCall!.Name}`{name.Value}"]);
                } else {
                  // We only suggest variables in scope.
                  var hints = new List<string>();
                  hints.AddRange(Scope.Names
                    .Where(n => n != null).Select(n => $"locals`{n}"));
                  hints.AddRange(EnclosingInputParameterFormals.Names
                    .Where(n => n != null).Select(n => $"{EnclosingMethodCall!.Name}`{n}"));
                  hint = DidYouMeanOneOf(hints);
                }
                ReportError(fieldLocation, "variable '{0}' is not declared{1}", name, hint);
                fieldLocation.PreType = CreatePreTypeProxy("field-location");
                return;
              }
              if (v is not LocalVariable local) {
                if (v is not Formal formal) {
                  ReportError(fieldLocation, "variable '{0}' is not a local variable or a method parameter", name);
                  fieldLocation.PreType = CreatePreTypeProxy("field-location");
                  return;
                }
                localField = formal.GetLocalField(method);
              } else {
                localField = local.GetLocalField(method);
              }
              resolved = CreateObjectFieldLocation(fieldLocation.Origin, fieldLocation.Lhs, fieldLocation.Name, localField, false);
              ResolveWith(localField, resolved);
              break;
            }

            if (innerCallEnclosingMethod != null) {
              // We raise an error and exit
              ReportError(fieldLocation.Name.Origin, "Method memory location requires the name to be a method input parameter");
              fieldLocation.PreType = CreatePreTypeProxy("field-location");
              break;
            }
            var lhsObjType = fieldLocation.Lhs.PreType;
            lhsObjType = Constraints.FindDefinedPreType(lhsObjType, true) ?? lhsObjType;
            var innerLhsObjType = InnerTypeForBacktickLhs(lhsObjType);
            var receiver = new IdentifierExpr(expr.Origin, "tmp") {
              PreType = innerLhsObjType
            };

            var tmpDotSuffix =
              new ExprDotName(fieldLocation.Origin, receiver, fieldLocation.Name, null);
            var dotSuffix = ResolveDotSuffix(tmpDotSuffix,
              false, true, [], resolutionContext, false);

            dotSuffix ??= tmpDotSuffix.ResolvedExpression;
            if (dotSuffix is not MemberSelectExpr memberSelect) {
              ReportError(fieldLocation,
                $"Expected member selection, but got {dotSuffix?.GetType()}");
              fieldLocation.PreType = CreatePreTypeProxy("field-location");
              return;
            }

            if (memberSelect.Member is not Field field) {
              ReportError(fieldLocation,
                $"Expected constant or mutable field reference, but got {memberSelect.Member.WhatKind}");
              fieldLocation.PreType = CreatePreTypeProxy("field-location");
              return;
            }

            if (lhsObjType.IsRefType) {
              resolved = CreateObjectFieldLocation(fieldLocation.Origin, fieldLocation.Lhs, fieldLocation.Name, field, false);
            } else {
              innerLhsObjType = Constraints.FindDefinedPreType(innerLhsObjType, true) ?? innerLhsObjType;
              resolved = MemoryLocationSetComprehension(fieldLocation.Origin, innerLhsObjType, fieldLocation.Lhs,
                o => (
                  CreateObjectFieldLocation(fieldLocation.Origin, o, fieldLocation.Name, field, false),
                  new ExprDotName(fieldLocation.Origin, o, fieldLocation.Name, null))
                  );
            }

            ResolveExpression(resolved, resolutionContext);
            fieldLocation.ResolvedExpression = resolved;
            fieldLocation.PreType = resolved.PreType;
            fieldLocation.ResolvedField = field;

            break;
          }
        case IndexFieldLocationExpression indexFieldLocation: {
            ResolveExpression(indexFieldLocation.Lhs, resolutionContext);
            var lhsObjType = indexFieldLocation.Lhs.PreType;
            lhsObjType = Constraints.FindDefinedPreType(lhsObjType, true) ?? lhsObjType;
            var innerLhsObjType = InnerTypeForBacktickLhs(lhsObjType);
            innerLhsObjType = Constraints.FindDefinedPreType(innerLhsObjType, true) ?? innerLhsObjType;

            var receiver = new IdentifierExpr(expr.Origin, "tmp") {
              PreType = innerLhsObjType
            };

            var arrayDims = 1;
            if (receiver.PreType is not DPreType { Decl.Name: var arrayName } arrayType
                || !arrayName.StartsWith(PreType.TypeNameArray) ||
                arrayName != PreType.TypeNameArray
                && !int.TryParse(arrayName.AsSpan(PreType.TypeNameArray.Length), out arrayDims)) {
              ReportError(indexFieldLocation,
                $"Expected array memory location to be applied to an array, but got {receiver}");
              indexFieldLocation.PreType = CreatePreTypeProxy("index-field-location");
              return;
            }
            if (arrayDims != indexFieldLocation.Indices.Count) {
              ReportError(indexFieldLocation,
                $"Expected {arrayDims} {(arrayDims > 1 ? "indices" : "index")}, but got {indexFieldLocation.Indices.Count}");
              indexFieldLocation.PreType = CreatePreTypeProxy("index-field-location");
            }

            foreach (var subexpr in indexFieldLocation.Indices) {
              ResolveExpression(subexpr, resolutionContext);
              ConstrainToIntFamily(subexpr.PreType, subexpr.Origin, "Expected int, but got {0}");
            }



            Expression resolved;
            if (lhsObjType.Normalize().IsRefType) {
              resolved = CreateObjectIndexFieldLocation(indexFieldLocation.Origin, indexFieldLocation.Lhs, indexFieldLocation.Indices, indexFieldLocation.OpenParen, indexFieldLocation.CloseParen);
            } else {
              innerLhsObjType = Constraints.FindDefinedPreType(innerLhsObjType, true) ?? innerLhsObjType;
              resolved = MemoryLocationSetComprehension(indexFieldLocation.Origin, innerLhsObjType, indexFieldLocation.Lhs,
                o =>
                  (CreateObjectIndexFieldLocation(indexFieldLocation.Origin, o, indexFieldLocation.Indices,
                  indexFieldLocation.OpenParen, indexFieldLocation.CloseParen),
                    indexFieldLocation.Indices.Count == 1 ?
                      new SeqSelectExpr(indexFieldLocation.Origin, true, o, indexFieldLocation.Indices[0], null, null) :
                      new MultiSelectExpr(indexFieldLocation.Origin, o, indexFieldLocation.Indices)
                    ));
            }

            ResolveExpression(resolved, resolutionContext);
            indexFieldLocation.ResolvedExpression = resolved;
            indexFieldLocation.PreType = resolved.PreType;
            break;
          }
        case FieldLocation fLoc: {
            fLoc.PreType = Type2PreType(Type.Field);
            fLoc.Type = Type.Field;
            break;
          }
        case IndexFieldLocation ifLoc: {
            ifLoc.PreType = Type2PreType(Type.Field);
            ifLoc.Type = Type.Field;
            break;
          }
        case NestedMatchExpr matchExpr: {
            var e = matchExpr;
            ResolveNestedMatchExpr(e, resolutionContext);
            break;
          }
        case MatchExpr: {
            Contract.Assert(false); // this case is always handled via NestedMatchExpr
            break;
          }
        case LocalsObjectExpression locals:
          locals.PreType = new DPreType(BuiltInTypeDecl(PreType.TypeNameObjectQ), []);
          var objectQDecl = resolver.ProgramResolver.Program.SystemModuleManager.ObjectDecl.NonNullTypeDecl;
          var localsType = new UserDefinedType(locals.Origin, objectQDecl.Name, objectQDecl, []);
          locals.Type = localsType;
          break;
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected expression
      }

      if (expr.PreType == null) {
        // some resolution error occurred
        expr.PreType = CreatePreTypeProxy("ResolveExpression didn't compute this pre-type");
      }
    }

    private static string DidYouMeanOneOf(List<string> hints) {
      return hints.Count > 1
        ? " - did you mean one of " + string.Join(", ", hints.Take(hints.Count - 1)) + ", or " + hints.Last()
        : hints.Count == 1
          ? " - did you mean " + hints.FirstOrDefault() : "";
    }

    private static PreType InnerTypeForBacktickLhs(PreType lhsObjType) {
      PreType innerLhsObjType;
      if (lhsObjType.Normalize() is DPreType {
        Decl.Name: PreType.TypeNameSet or PreType.TypeNameSeq or PreType.TypeNameMultiset,
        Arguments: [var arg]
      } dpt) {
        innerLhsObjType = arg;
      } else {
        innerLhsObjType = lhsObjType;
      }

      return innerLhsObjType;
    }


    // Returns also the trigger obj.fieldName
    private static DatatypeValue CreateObjectFieldLocation(IOrigin origin, Expression obj, Name fieldName, Field field, bool atCallSite) {
      return new DatatypeValue(origin, SystemModuleManager.TupleTypeName([false, false]), SystemModuleManager.TupleTypeCtorName(2),
        [obj, new FieldLocation(fieldName, field, atCallSite) { Type = Type.Field }]);
    }

    private static DatatypeValue CreateObjectIndexFieldLocation(IOrigin origin, Expression obj,
      List<Expression> indices, Token openParen, Token closeParen) {
      return new DatatypeValue(origin, SystemModuleManager.TupleTypeName([false, false]), SystemModuleManager.TupleTypeCtorName(2),
        [obj, new IndexFieldLocation(obj, openParen, indices, closeParen) { Type = Type.Field }]);
    }

    private static Expression MemoryLocationSetComprehension(IOrigin tok, PreType innerLhsObjType, Expression collection,
      Func<IdentifierExpr, (DatatypeValue, Expression trigger)> getTermTrigger) // TODO: make termFromBoundIdentifier return possible triggers like MemberSelectExpr
    {
      var pt = (DPreType)innerLhsObjType.Normalize();
      var arguments = pt.Arguments.ConvertAll(PreType2TypeUtil.PreType2RefinableType);
      // We don't accept 'null' in set comprehensions, so we can't just use PreType2TypeUtil.PreType2Type
      // that would otherwise return a '?';
      var c = pt.Decl is ClassLikeDecl cd ? cd.NonNullTypeDecl : pt.Decl;
      var userDefinedType = new UserDefinedType(pt.Decl.Origin, pt.Decl.Name, c, arguments);

      var bv = new BoundVar(tok, "_x", userDefinedType);
      var termExpr = new IdentifierExpr(tok, bv);
      var termTrigger = getTermTrigger(termExpr);
      var term = termTrigger.Item1;
      var trigger = termTrigger.trigger;
      var resolved = new SetComprehension(tok, true, [bv],
        new BinaryExpr(tok, BinaryExpr.Opcode.In, termExpr, collection),
        term);
      resolved.Attributes = new Attributes("trigger", [term], new Attributes("trigger", [trigger], null));
      return resolved;
    }

    private void ResolveCollectionProducingExpr(string typeName, string exprKindSuffix, Expression expr, PreType elementPreType,
      PreTypeConstraints.CommonConfirmationBag confirmationFamily, bool isStringType = false) {
      var exprKind = isStringType ? exprKindSuffix : $"{typeName} {exprKindSuffix}";
      SetupCollectionProducingExpr(typeName, isStringType, exprKind, expr, elementPreType);
      AddConfirmation(confirmationFamily, expr.PreType, expr.Origin, $"{exprKind} used as if it had type {{0}}");
    }

    private void ResolveMapProducingExpr(bool finite, string exprKindSuffix, Expression expr, PreType keyPreType, PreType valuePreType) {
      var typeName = PreType.MapTypeName(finite);
      PreTypeConstraints.CommonConfirmationBag confirmationFamily =
        finite ? PreTypeConstraints.CommonConfirmationBag.InMapFamily : PreTypeConstraints.CommonConfirmationBag.InImapFamily;
      var exprKind = $"{typeName} {exprKindSuffix}";

      SetupCollectionProducingExpr(typeName, false, exprKind, expr, keyPreType, valuePreType);
      AddConfirmation(confirmationFamily, expr.PreType, expr.Origin, $"{exprKind} used as if it had type {{0}}");
    }

    private void SetupCollectionProducingExpr(string typeName, bool isStringType, string exprKind, Expression expr, PreType elementPreType, PreType valuePreType = null) {
      expr.PreType = CreatePreTypeProxy(exprKind);

      var arguments = valuePreType == null ? [elementPreType] : new List<PreType>() { elementPreType, valuePreType };
      var defaultType = new DPreType(BuiltInTypeDecl(typeName), arguments,
        isStringType ? new DPreType(BuiltInTypeDecl(PreType.TypeNameString), []) : null);
      Constraints.AddDefaultAdvice(expr.PreType, defaultType);

      Constraints.AddGuardedConstraint(() => {
        if (expr.PreType.UrAncestor(this) is DPreType dPreType && dPreType.Decl.Name == typeName) {
          if (valuePreType == null) {
            AddSubtypeConstraint(dPreType.Arguments[0], elementPreType, expr.Origin,
              $"element type of {exprKind} expected to be {{0}} (got {{1}})");
          } else {
            AddSubtypeConstraint(dPreType.Arguments[0], elementPreType, expr.Origin,
              $"key type of {exprKind} expected to be {{0}} (got {{1}})");
            AddSubtypeConstraint(dPreType.Arguments[1], valuePreType, expr.Origin,
              $"value type of {exprKind} expected to be {{0}} (got {{1}})");
          }
          return true;
        }
        return false;
      });
    }

    private PreType ResolveBinaryExpr(IOrigin tok, BinaryExpr.Opcode opcode, Expression e0, Expression e1, ResolutionContext resolutionContext) {
      var opString = BinaryExpr.OpcodeString(opcode);
      PreType resultPreType = null;
      switch (opcode) {
        case BinaryExpr.Opcode.Iff:
        case BinaryExpr.Opcode.Imp:
        case BinaryExpr.Opcode.Exp:
        case BinaryExpr.Opcode.And:
        case BinaryExpr.Opcode.Or: {
            resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
            ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
            break;
          }

        case BinaryExpr.Opcode.Eq:
        case BinaryExpr.Opcode.Neq:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          AddComparableConstraint(e0.PreType, e1.PreType, tok, false, "arguments must have comparable types (got {0} and {1})");
          break;

        case BinaryExpr.Opcode.Disjoint:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, null);
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.Disjointable, e0.PreType, tok, "arguments must be of a set or multiset type (got {0})");
          break;

        case BinaryExpr.Opcode.Lt:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          Constraints.AddGuardedConstraint(() => {
            var left = e0.PreType.NormalizeWrtScope() as DPreType;
            var right = e1.PreType.NormalizeWrtScope() as DPreType;
            if (left is { Decl: IndDatatypeDecl or TypeParameter }) {
              AddConfirmation(PreTypeConstraints.CommonConfirmationBag.RankOrderable, e1.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {e0.PreType} and {{0}})");
              return true;
            } else if (right is { Decl: IndDatatypeDecl }) {
              AddConfirmation(PreTypeConstraints.CommonConfirmationBag.RankOrderableOrTypeParameter, e0.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {{0}} and {e1.PreType})");
              return true;
            } else if (left != null || right != null) {
              var commonSupertype = CreatePreTypeProxy("common supertype of < operands");
              ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, commonSupertype);
              AddConfirmation(PreTypeConstraints.CommonConfirmationBag.OrderableLess, e0.PreType, tok,
                "arguments to " + opString +
                " must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0})");
              return true;
            }
            return false;
          });
          break;

        case BinaryExpr.Opcode.Le:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, null);
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.OrderableLess, e0.PreType, tok,
            "arguments to " + opString +
            " must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0})");
          break;

        case BinaryExpr.Opcode.Gt:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          Constraints.AddGuardedConstraint(() => {
            var left = e0.PreType.NormalizeWrtScope() as DPreType;
            var right = e1.PreType.NormalizeWrtScope() as DPreType;
            if (left is { Decl: IndDatatypeDecl }) {
              AddConfirmation(PreTypeConstraints.CommonConfirmationBag.RankOrderableOrTypeParameter, e1.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {e0.PreType} and {{0}})");
              return true;
            } else if (right != null && (right.Decl is IndDatatypeDecl || right.Decl is TypeParameter)) {
              AddConfirmation(PreTypeConstraints.CommonConfirmationBag.RankOrderable, e0.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {{0}} and {e1.PreType})");
              return true;
            } else if (left != null || right != null) {
              var commonSupertype = CreatePreTypeProxy("common supertype of < operands");
              ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, commonSupertype);
              AddConfirmation(PreTypeConstraints.CommonConfirmationBag.OrderableGreater, e0.PreType, tok,
                "arguments to " + opString + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0})");
              return true;
            }
            return false;
          });
          break;

        case BinaryExpr.Opcode.Ge:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, null);
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.OrderableGreater, e0.PreType, tok,
            "arguments to " + opString + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0})");
          break;

        case BinaryExpr.Opcode.Add:
          if (!TryApplyFp64ArithmeticConstraints(e0, e1, tok, ref resultPreType)) {
            resultPreType = CreatePreTypeProxy("result of +");
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.Plussable, resultPreType, tok,
              "type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like or map-like type (instead got {0})");
            ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          }
          break;

        case BinaryExpr.Opcode.Sub:
          if (!TryApplyFp64ArithmeticConstraints(e0, e1, tok, ref resultPreType)) {
            resultPreType = CreatePreTypeProxy("result of -");
            Constraints.AddGuardedConstraint(() => {
              // The following cases are allowed (fp64 is handled above):
              // Uniform cases:
              //   - int int
              //   - real real
              //   - bv bv
              //   - ORDINAL ORDINAL
              //   - char char
              //   - set<T> set<V>
              //   - iset<T> iset<V>
              //   - multiset<T> multiset<T>
              // Non-uniform cases:
              //   - map<T, U> set<V>
              //   - imap<T, U> set<V>
              //
              // The tests below distinguish between the uniform and non-uniform cases, but otherwise may allow some cases
              // that are not included above. The after the enclosing call to AddGuardedConstraint will arrange to confirm
              // that only the expected types are allowed.
              var a0 = e0.PreType;
              var a1 = e1.PreType;
              var familyDeclNameLeft = AncestorName(a0);
              var familyDeclNameRight = AncestorName(a1);

              if (familyDeclNameLeft is PreType.TypeNameMap or PreType.TypeNameImap) {
                var left = (DPreType)a0.UrAncestor(this);
                Contract.Assert(left.Arguments.Count == 2);
                var st = new DPreType(BuiltInTypeDecl(PreType.TypeNameSet), [left.Arguments[0]]);
                Constraints.DebugPrint($"    guard applies: Minusable {a0} {a1}, converting to {st} :> {a1}");
                Constraints.AddDefaultAdvice(a1, st);

                var messageFormat = $"map subtraction expects right-hand operand to have type {st} (instead got {{0}})";
                Constraints.AddGuardedConstraint(() => {
                  if (a1.UrAncestor(this) is DPreType dPreType) {
                    if (dPreType.Decl.Name != PreType.TypeNameSet) {
                      ReportError(e1, messageFormat, a1);
                    } else {
                      AddSubtypeConstraint(dPreType.Arguments[0], left.Arguments[0], e1.Origin,
                        $"element type of {PreType.TypeNameSet} expected to be {{0}} (got {{1}})");
                    }
                    return true;
                  }
                  return false;
                });
                AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InSetFamily, a1, e1.Origin, messageFormat);
                return true;
              } else if (familyDeclNameLeft != null || (familyDeclNameRight != null && familyDeclNameRight != PreType.TypeNameSet)) {
                Constraints.DebugPrint($"    guard applies: Minusable {a0} {a1}, converting to {a0} :> {a1}");
                AddSubtypeConstraint(a0, a1, tok, "type of right argument to - ({0}) must agree with the result type ({1})");
                return true;
              }
              return false;
            });
            ConstrainOperandTypes(tok, opString, e0, null, resultPreType);
          }
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.Minusable, resultPreType, tok,
            "type of - must be of a numeric type, a bitvector type, ORDINAL, char, or a set-like or map-like type (instead got {0})");
          break;

        case BinaryExpr.Opcode.Mul:
          if (!TryApplyFp64ArithmeticConstraints(e0, e1, tok, ref resultPreType)) {
            resultPreType = CreatePreTypeProxy("result of *");
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.Mullable, resultPreType, tok,
              "type of * must be of a numeric type, bitvector type, or a set-like type (instead got {0})");
            ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          }
          break;

        case BinaryExpr.Opcode.In:
        case BinaryExpr.Opcode.NotIn:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, "'" + opString + "'");
          Constraints.AddGuardedConstraint(() => {
            // For "Innable x s", if s is known, then:
            // if s == c<a> or s == c<a, b> where c is a collection type, then a ~~ x, else error.
            var a0 = e0.PreType.NormalizeWrtScope();
            var a1 = e1.PreType.NormalizeWrtScope();
            var coll = a1.UrAncestor(this).AsCollectionPreType();
            if (coll != null) {
              Constraints.DebugPrint($"    guard applies: Innable {a0} {a1}");
              AddComparableConstraint(coll.Arguments[0], a0, tok, false, "expecting element type to be assignable to {0} (got {1})");
              return true;
            } else if (a1 is DPreType) {
              // type head is determined and it isn't a collection type
              ReportError(tok,
                $"second argument to '{opString}' must be a set, a multiset, " +
                $"a sequence with elements of type {e0.PreType}, or a map with domain {e0.PreType} (instead got {e1.PreType})");
              return true;
            }
            return false;
          });
          break;

        case BinaryExpr.Opcode.Div:
          if (!TryApplyFp64ArithmeticConstraints(e0, e1, tok, ref resultPreType)) {
            resultPreType = CreatePreTypeProxy("result of / operation");
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.NumericOrBitvector, resultPreType, tok, "arguments to " + opString + " must be numeric or bitvector types (got {0})");
            ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          }
          break;

        case BinaryExpr.Opcode.Mod:
          resultPreType = CreatePreTypeProxy("result of % operation");
          ConstrainToIntFamilyOrBitvector(resultPreType, tok, "type of " + opString + " must be integer-numeric or bitvector types (got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.BitwiseAnd:
        case BinaryExpr.Opcode.BitwiseOr:
        case BinaryExpr.Opcode.BitwiseXor:
          resultPreType = CreatePreTypeProxy("result of " + opString + " operation");
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IsBitvector, resultPreType, tok, "type of " + opString + " must be of a bitvector type (instead got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.LeftShift:
        case BinaryExpr.Opcode.RightShift: {
            resultPreType = CreatePreTypeProxy("result of " + opString + " operation");
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IsBitvector, resultPreType, tok, "type of " + opString + " must be of a bitvector type (instead got {0})");
            ConstrainOperandTypes(tok, opString, e0, null, resultPreType);
            AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IntLikeOrBitvector, e1.PreType, tok,
              "type of right argument to " + opString + " ({0}) must be an integer-numeric or bitvector type");
            break;
          }

        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException(); // unexpected operator
      }
      // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
      // setting e.ResolvedOp until inside CheckTypeInference.
      return resultPreType;
    }

    public void ConstrainTypeExprBool(Expression e, string msgFormat) {
      Contract.Requires(e != null);
      Contract.Requires(msgFormat != null);  // may have a {0} part
      if (e.PreType != null) {
        ConstrainExpressionToBoolFamily(e, msgFormat);
      } else {
        e.PreType = ConstrainResultToBoolFamily(e.Origin, "<unspecified use>", msgFormat);
      }
    }

    private PreType ConstrainResultToBoolFamilyOperator(IOrigin tok, string opString) {
      var proxyDescription = $"result of {opString} operation";
      return ConstrainResultToBoolFamily(tok, proxyDescription, "type of " + opString + " must be a boolean (got {0})");
    }

    private PreType ConstrainResultToBoolFamily(IOrigin tok, string proxyDescription, string errorFormat) {
      var pt = CreatePreTypeProxy(proxyDescription);
      Constraints.AddDefaultAdvice(pt, CommonAdvice.Target.Bool);
      AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InBoolFamily, pt, tok, errorFormat);
      return pt;
    }

    private void ConstrainExpressionToBoolFamily(Expression expr, string errorFormat) {
      Contract.Assert(expr.PreType != null);
      Constraints.AddDefaultAdvice(expr.PreType, CommonAdvice.Target.Bool);
      AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InBoolFamily, expr.PreType, expr.Origin, errorFormat);
    }

    private void ConstrainToIntFamily(PreType preType, IOrigin tok, string errorFormat) {
      Constraints.AddDefaultAdvice(preType, CommonAdvice.Target.Int);
      AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InIntFamily, preType, tok, errorFormat);
    }

    private void ConstrainToIntFamilyOrBitvector(PreType preType, IOrigin tok, string errorFormat) {
      Constraints.AddDefaultAdvice(preType, CommonAdvice.Target.Int);
      AddConfirmation(PreTypeConstraints.CommonConfirmationBag.IntLikeOrBitvector, preType, tok, errorFormat);
    }

    private void ConstrainToCommonSupertype(IOrigin tok, string opString, PreType a, PreType b, PreType commonSupertype) {
      if (commonSupertype == null) {
        commonSupertype = CreatePreTypeProxy($"element type of common {opString} supertype");
      }
      var errorFormat = $"arguments to {opString} must have a common supertype (got {{0}} and {{1}})";
      AddSubtypeConstraint(commonSupertype, a, tok, errorFormat);
      AddSubtypeConstraint(commonSupertype, b, tok, errorFormat);
    }

    private void ConstrainOperandTypes(IOrigin tok, string opString, Expression e0, Expression e1, PreType resultPreType) {
      if (e0 != null) {
        AddSubtypeConstraint(resultPreType, e0.PreType, tok,
          $"type of left argument to {opString} ({{1}}) must agree with the result type ({{0}})");
      }
      if (e1 != null) {
        AddSubtypeConstraint(resultPreType, e1.PreType, tok,
          $"type of right argument to {opString} ({{1}}) must agree with the result type ({{0}})");
      }
    }

    /// <summary>
    /// Resolve "memberName" in what currently is known as "receiverPreType". If "receiverPreType" is an unresolved
    /// proxy type, try to solve enough type constraints and use heuristics to figure out which type contains
    /// "memberName" and return that enclosing type as "tentativeReceiverType". However, try not to make
    /// type-inference decisions about "receiverPreType"; instead, lay down the further constraints that need to
    /// be satisfied in order for "tentativeReceiverType" to be where "memberName" is found.
    /// Consequently, if "memberName" is found and returned as a "MemberDecl", it may still be the case that
    /// "receiverPreType" is an unresolved proxy type and that, after solving more type constraints, "receiverPreType"
    /// eventually gets set to a type more specific than "tentativeReceiverType".
    /// </summary>
    (MemberDecl /*?*/, DPreType /*?*/) FindMember(IOrigin tok, PreType receiverPreType, string memberName, ResolutionContext resolutionContext,
      bool reportErrorOnMissingMember = true) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverPreType != null);
      Contract.Requires(memberName != null);

      var dReceiver = Constraints.ApproximateReceiverType(receiverPreType, memberName);
      if (dReceiver == null) {
        if (reportErrorOnMissingMember) {
          ReportError(tok, "type of the receiver is not fully determined at this program point");
        }

        return (null, null);
      }

      var receiverDecl = dReceiver.DeclWithMembersBypassInternalSynonym();
      if (receiverDecl is TopLevelDeclWithMembers receiverDeclWithMembers) {

        var members = resolver.GetClassMembers(receiverDeclWithMembers);
        if (members == null || !members.TryGetValue(memberName, out var member)) {
          if (!reportErrorOnMissingMember) {
            // don't report any error
          } else if (memberName == "_ctor") {
            ReportError(tok, $"{receiverDecl.WhatKind} '{receiverDecl.Name}' does not have an anonymous constructor");
          } else {
            ReportMemberNotFoundError(tok, memberName, members, receiverDecl, resolutionContext);
          }
          return (null, null);
        } else if (resolver.VisibleInScope(member)) {
          // TODO: We should return the original "member", not an overridden member. Alternatively, we can just return "member" so that the
          // caller can figure out the types, and then a later pass can figure out which particular "member" is intended.
          return (member, dReceiver);
        } else if (reportErrorOnMissingMember) {
          ReportError(tok, $"member '{memberName}' has not been imported in this scope and cannot be accessed here");
          return (null, null);
        }
      }
      if (reportErrorOnMissingMember) {
        ReportMemberNotFoundError(tok, memberName, null, receiverDecl, resolutionContext);
      }
      return (null, null);
    }

    private void ReportMemberNotFoundError(IOrigin tok, string memberName, [CanBeNull] Dictionary<string, MemberDecl> members,
      TopLevelDecl receiverDecl, ResolutionContext resolutionContext) {
      if (memberName.StartsWith(HideRevealStmt.RevealLemmaPrefix)) {
        var nameToBeRevealed = memberName[HideRevealStmt.RevealLemmaPrefix.Length..];
        if (members == null) {
          if (receiverDecl is TopLevelDeclWithMembers receiverDeclWithMembers) {
            // try this instead:
            members = resolver.GetClassMembers(receiverDeclWithMembers);
          }
        }
        if (members == null) {
          ReportError(tok, $"member '{nameToBeRevealed}' does not exist in {receiverDecl.WhatKindAndName}");
        } else if (!members.TryGetValue(nameToBeRevealed, out var member)) {
          ReportError(tok, $"member '{nameToBeRevealed}' does not exist in {receiverDecl.WhatKindAndName}");
        } else if (member is not (ConstantField or Function)) {
          Contract.Assert(!member.IsOpaque);
          ReportError(tok,
            $"a {member.WhatKind} ('{nameToBeRevealed}') cannot be revealed; only opaque constants and functions can be revealed");
        } else if (!member.IsOpaque) {
          ReportError(tok, $"{member.WhatKind} '{nameToBeRevealed}' cannot be revealed, because it is not opaque");
        } else if (member is Function { Body: null }) {
          ReportError(tok,
            $"{member.WhatKind} '{nameToBeRevealed}' cannot be revealed, because it has no body in {receiverDecl.WhatKindAndName}");
        } else {
          ReportError(tok, $"cannot reveal '{nameToBeRevealed}'");
        }
      } else {
        ReportError(tok, $"member '{memberName}' does not exist in {receiverDecl.WhatKindAndName}");
      }
    }

    public Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
      ResolutionContext resolutionContext, bool allowMethodCall, bool complain = true) {
      return ResolveNameSegment(expr, isLastNameSegment, args, resolutionContext, allowMethodCall, out _, complain, false);
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Local variable, parameter, or bound variable.
    ///     (Language design note:  If this clashes with something of interest, one can always rename the local variable locally.)
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. If isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module (if two constructors have the same name, an error message is produced here)
    ///     (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor
    ///     name with the name of the datatype.)
    ///  3. Member of the enclosing module (type name or the name of a module)
    ///  4. Static function or method in the enclosing module or its imports
    ///  5. If !isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module
    ///
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the NameSegment is not directly enclosed in another NameSegment or ExprDotName expression.</param>
    /// <param name="args">If the NameSegment is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="resolutionContext"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a MemberSelectExpr whose .Member is a Method.</param>
    /// <param name="shadowedModule">See description of method CheckForAmbiguityInShadowedImportedModule.</param>
    /// <param name="complain"></param>
    /// <param name="specialOpaqueHackAllowance">If "true", treats an expression "f" where "f" is an instance function, as "this.f", even though
    /// there is no "this" in scope. This seems like a terrible hack, because it breaks scope invariants about the AST. But, for now, it's here
    /// to mimic what the legacy resolver does.</param>
    public Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
      ResolutionContext resolutionContext, bool allowMethodCall, out ModuleDecl shadowedModule, bool complain, bool specialOpaqueHackAllowance) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      shadowedModule = null;

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          resolver.ResolveType(expr.Origin, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      // For 1 and 4:
      MemberDecl member = null;
      // For 2 and 5:
      Tuple<DatatypeCtor, bool> pair;

      var name = resolutionContext.InReveal ? HideRevealStmt.RevealLemmaPrefix + expr.Name : expr.Name;
      var v = scope.Find(name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          if (complain) {
            ReportError(expr.Origin, "variable '{0}' does not take any type parameters", name);
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        }
        r = new IdentifierExpr(expr.Origin, v) {
          PreType = v.PreType
        };
      } else if (currentClass != null && resolver.GetClassMembers(currentClass) is { } members &&
                 members.TryGetValue(name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.Origin, UserDefinedType.FromTopLevelDecl(expr.Origin, currentClass, currentClass.TypeArgs),
            (TopLevelDeclWithMembers)member.EnclosingClass, true);
          receiver.PreType = Type2PreType(receiver.Type);
        } else {
          if (!scope.AllowInstance && !specialOpaqueHackAllowance) {
            if (complain) {
              ReportError(expr.Origin, "'this' is not allowed in a 'static' context"); //TODO: Rephrase this
            } else {
              expr.ResolvedExpression = null;
              return null;
            }
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.Origin);
          receiver.Type = ModuleResolver.GetThisType(expr.Origin, currentClass);
          receiver.PreType = Type2PreType(receiver.Type);
        }
        r = ResolveExprDotCall(expr.Origin, new Name(expr.Origin, expr.Name), receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);

      } else if (isLastNameSegment && resolver.moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 2. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          if (!complain) {
            return null;
          }
        }

      } else if (name is "fp32" or "fp64") {
        // Special handling for float types (on-demand initialization)
        var variety = name == "fp32" ? ValuetypeVariety.Fp32 : ValuetypeVariety.Fp64;
        if (name == "fp32") {
          resolver.ProgramResolver.SystemModuleManager.EnsureFloatTypesInitialized(resolver.ProgramResolver);
        } else {
          resolver.ProgramResolver.SystemModuleManager.EnsureFp64TypeInitialized(resolver.ProgramResolver);
        }
        var floatDecl = resolver.ProgramResolver.SystemModuleManager.valuetypeDecls[(int)variety];

        // Add to moduleInfo.TopLevels for future lookups
        if (!resolver.moduleInfo.TopLevels.ContainsKey(name)) {
          resolver.moduleInfo.TopLevels[name] = floatDecl;
        }

        r = CreateResolver_IdentifierExpr(expr.Origin, name, expr.OptTypeArguments, floatDecl);

      } else if (resolver.moduleInfo.TopLevels.TryGetValue(name, out var decl)) {
        // ----- 3. Member of the enclosing module

        // Record which imported module, if any, was shadowed by `name` in the current module.
        shadowedModule = resolver.moduleInfo.ShadowedImportedModules.GetValueOrDefault(name);

        if (decl is AmbiguousTopLevelDecl ambiguousTopLevelDecl) {
          if (complain) {
            ReportError(expr.Origin,
              "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)",
              expr.Name, ambiguousTopLevelDecl.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          // We have found a module name or a type name, neither of which is an expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into an expression. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          if (!isLastNameSegment) {
            if (decl is ClassLikeDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
              // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
              // the name of the class, C. Report an error and continue.
              if (complain) {
                ReportError(expr.Origin, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              } else {
                expr.ResolvedExpression = null;
                return null;
              }
            }
          }
          r = CreateResolver_IdentifierExpr(expr.Origin, name, expr.OptTypeArguments, decl);
        }

      } else if (resolver.moduleInfo.StaticMembers.TryGetValue(name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (member is AmbiguousMemberDecl ambiguousMember) {
          if (complain) {
            ReportError(expr.Origin, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ambiguousMember.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          var receiver = new StaticReceiverExpr(expr.Origin, (TopLevelDeclWithMembers)member.EnclosingClass, true);
          receiver.PreType = Type2PreType(receiver.Type);
          r = ResolveExprDotCall(expr.Origin, new Name(expr.Origin, expr.Name), receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
        }

      } else if (!isLastNameSegment && resolver.moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 5. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          if (!complain) {
            return null;
          }
        }

      } else {
        // ----- None of the above
        if (complain) {
          ReportUnresolvedIdentifierError(expr.Origin, name, resolutionContext);
        } else {
          expr.ResolvedExpression = null;
          return null;
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .PreType
        expr.PreType = CreatePreTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        if (r.Type != null) {
          // The following may be needed to meet some .WasResolved() expectations
          expr.Type = r.Type.UseInternalSynonym();
        }
        expr.PreType = r.PreType;
      }
      return rWithArgs;
    }

    private void ReportUnresolvedIdentifierError(IOrigin tok, string name, ResolutionContext resolutionContext) {
      if (resolutionContext.InReveal) {
        var nameToReport = name.StartsWith(HideRevealStmt.RevealLemmaPrefix) ? name[HideRevealStmt.RevealLemmaPrefix.Length..] : name;
        ReportError(tok,
          "cannot reveal '{0}' because no revealable constant, function, assert label, or requires label in the current scope is named '{0}'",
          nameToReport);
      } else {
        ReportError(tok, "unresolved identifier: {0}", name);
      }
    }

    private ResolverIdentifierExpr CreateResolver_IdentifierExpr(IOrigin tok, string name, List<Type> optTypeArguments, TopLevelDecl decl) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<ResolverIdentifierExpr>() != null);

      if (!resolver.moduleInfo.IsAbstract) {
        if (decl is ModuleDecl md && md.Signature.IsAbstract) {
          ReportError(tok, $"a compiled module is not allowed to use an abstract module ({decl.Name})");
        }
      }
      var n = optTypeArguments == null ? 0 : optTypeArguments.Count;
      if (optTypeArguments != null) {
        // type arguments were supplied; they must be equal in number to those expected
        if (n != decl.TypeArgs.Count) {
          ReportError(tok, $"Wrong number of type arguments ({n} instead of {decl.TypeArgs.Count}) passed to {decl.WhatKind}: {name}");
        }
      }
      var typeArguments = new List<Type>();
      for (var i = 0; i < decl.TypeArgs.Count; i++) {
        typeArguments.Add(i < n ? optTypeArguments[i] : new InferredTypeProxy());
      }
      return new ResolverIdentifierExpr(tok, decl, typeArguments);
    }

    private bool ResolveDatatypeConstructor(NameSegment expr, List<ActualBinding>/*?*/ args, ResolutionContext resolutionContext, bool complain,
      Tuple<DatatypeCtor, bool> pair, string name, ref Expression r, ref Expression rWithArgs) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

      var datatypeDecl = pair.Item1.EnclosingDatatype;
      if (pair.Item2) {
        // there is more than one constructor with this name
        if (complain) {
          ReportError(expr.Origin,
            "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')",
            expr.Name, datatypeDecl.Name);
          return false;
        } else {
          expr.ResolvedExpression = null;
          return true;
        }
      }

      if (expr.OptTypeArguments != null) {
        if (complain) {
          var errorMsg = $"datatype constructor does not take any type parameters ('{name}')";
          if (datatypeDecl.TypeArgs.Count != 0) {
            // Perhaps the user intended to put the type arguments on the constructor, but didn't know the right syntax.
            // Let's give a hint (whether or not expr.OptTypeArguments.Count == datatypeDecl.TypeArgs.Count).
            var givenTypeArguments = Util.Comma(expr.OptTypeArguments, targ => targ.ToString());
            errorMsg = $"{errorMsg}; did you perhaps mean to write '{datatypeDecl.Name}<{givenTypeArguments}>.{name}'?";
          }
          ReportError(expr.Origin, errorMsg);
          return false;
        } else {
          expr.ResolvedExpression = null;
          return true;
        }
      }

      ResolveDeclarationSignature(datatypeDecl);

      var rr = new DatatypeValue(expr.Origin, datatypeDecl.Name, name, args ?? []);
      var ok = ResolveDatatypeValue(resolutionContext, rr, datatypeDecl, null, complain);
      if (!ok) {
        expr.ResolvedExpression = null;
        return true;
      }
      if (args == null) {
        r = rr;
      } else {
        r = rr; // this doesn't really matter, since we're returning an "rWithArgs" (but it would have been proper to have returned the ctor as a lambda)
        rWithArgs = rr;
      }
      return false;
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. If isLastNameSegment:
    ///         Unambiguous constructor name of a datatype in module M (if two constructors have the same name, an error message is produced here)
    ///         (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///      1. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      2. Static function or method of M._default
    ///    (Note that in contrast to ResolveNameSegment, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      3. Look up id as a member of that type
    ///  * If E denotes an expression:
    ///      4. Let T be the type of E.  Look up id in T.
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the ExprDotName is not directly enclosed in another ExprDotName expression.</param>
    /// <param name="args">If the ExprDotName is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="resolutionContext"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a Resolver_MethodCall.</param>
    public Expression ResolveDotSuffix(ExprDotName expr, bool allowStaticReferenceToInstance, bool isLastNameSegment, List<ActualBinding> args, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      // resolve the LHS expression
      // LHS should not be reveal lemma
      ModuleDecl shadowedImport = null;
      ResolutionContext nonRevealOpts = resolutionContext with { InReveal = false };
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment((NameSegment)expr.Lhs, false, null, nonRevealOpts, allowMethodCall: false, out shadowedImport, complain: true, specialOpaqueHackAllowance: false);
      } else if (expr.Lhs is ExprDotName) {
        ResolveDotSuffix((ExprDotName)expr.Lhs, false, false, null, nonRevealOpts, false);
      } else {
        ResolveExpression(expr.Lhs, nonRevealOpts);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          resolver.ResolveType(expr.Origin, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      var name = resolutionContext.InReveal ? HideRevealStmt.RevealLemmaPrefix + expr.SuffixName : expr.SuffixName;
      var lhs = expr.Lhs.Resolved ?? expr.Lhs; // Sometimes resolution comes later, but pre-types have already been set
      if (lhs is { PreType: PreTypePlaceholderModule }) {
        var ri = (ResolverIdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).AccessibleSignature(false);
        sig = ModuleResolver.GetSignatureExt(sig);

        if (isLastNameSegment && sig.Ctors.TryGetValue(name, out var pair)) {
          // ----- 0. datatype constructor
          if (pair.Item2) {
            // there is more than one constructor with this name
            ReportError(expr.Origin, "the name '{0}' denotes a datatype constructor in module {2}, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", name, pair.Item1.EnclosingDatatype.Name, ((ModuleDecl)ri.Decl).Name);
          } else {
            if (expr.OptTypeArguments != null) {
              ReportError(expr.Origin, $"datatype constructor does not take any type parameters ('{name}')");
            }
            var rr = new DatatypeValue(expr.Origin, pair.Item1.EnclosingDatatype.Name, name, args ?? []);
            ResolveDatatypeValue(resolutionContext, rr, pair.Item1.EnclosingDatatype, null);

            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        } else if (sig.TopLevels.TryGetValue(name, out var decl)) {
          // ----- 1. Member of the specified module
          if (decl is AmbiguousTopLevelDecl) {
            var ad = (AmbiguousTopLevelDecl)decl;
            ReportError(expr.Origin, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ad.ModuleNames());
          } else {
            // We have found a module name or a type name, neither of which is an expression. However, the ExprDotName we're
            // looking at may be followed by a further suffix that makes this into an expression. We postpone the rest of the
            // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            if (!isLastNameSegment) {
              if (decl is ClassLikeDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
                // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
                // the name of the class, C. Report an error and continue.
                ReportError(expr.Origin, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              }
            }
            r = resolver.CreateResolver_IdentifierExpr(expr.Origin, name, expr.OptTypeArguments, decl);
          }
        } else if (sig.StaticMembers.TryGetValue(name, out var member)) {
          // ----- 2. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (member is AmbiguousMemberDecl) {
            var ambiguousMember = (AmbiguousMemberDecl)member;
            ReportError(expr.Origin, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ambiguousMember.ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.Origin, (TopLevelDeclWithMembers)member.EnclosingClass, true) {
              ContainerExpression = expr.Lhs
            };
            receiver.PreType = Type2PreType(receiver.Type);
            r = ResolveExprDotCall(expr.Origin, expr.SuffixNameNode, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        } else {
          ReportUnresolvedIdentifierError(expr.Origin, name, resolutionContext);
        }

      } else if (lhs is { PreType: PreTypePlaceholderType }) {
        var ri = (ResolverIdentifierExpr)lhs;
        // ----- 3. Look up name in type
        // expand any synonyms
        var ty = new UserDefinedType(expr.Origin, ri.Decl.Name, ri.Decl, ri.TypeArgs).NormalizeExpand();
        if (ty.IsDatatype) {
          // ----- LHS is a datatype
          var dt = ty.AsDatatype;
          if (dt.ConstructorsByName != null && dt.ConstructorsByName.TryGetValue(name, out var ctor)) {
            if (expr.OptTypeArguments != null) {
              ReportError(expr.Origin, $"datatype constructor does not take any type parameters ('{name}')");
            }

            var rr = new DatatypeValue(expr.Origin, ctor.EnclosingDatatype.Name, name, args ?? []);
            if (ri.TypeArgs.Count != 0) {
              rr.InferredTypeArgs = ri.TypeArgs;
            }
            ResolveDatatypeValue(resolutionContext, rr, ctor.EnclosingDatatype, (DPreType)Type2PreType(ty));

            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        }
        var cd = r == null ? ty.AsTopLevelTypeWithMembersBypassInternalSynonym : null;

        // Special handling for built-in types like fp32 and fp64
        if (cd == null && ty.IsFloatingPointType && ri.Decl is ValuetypeDecl valuetypeDecl) {
          cd = valuetypeDecl;
        }

        if (cd != null) {
          // ----- LHS is a type with members
          if (resolver.GetClassMembers(cd) is { } members && members.TryGetValue(name, out var member)) {
            if (!resolver.VisibleInScope(member)) {
              ReportError(expr.Origin, $"member '{name}' has not been imported in this scope and cannot be accessed here");
            }
            if (!member.IsStatic && !allowStaticReferenceToInstance) {
              ReportError(expr.Origin, $"accessing member '{name}' requires an instance expression");
              // nevertheless, continue creating an expression that approximates a correct one
            }
            // Create the appropriate type for the StaticReceiverExpr
            UserDefinedType receiverType;
            if (ty.IsFloatingPointType && ri.Decl is ValuetypeDecl vtDecl) {
              // For built-in types like fp32/fp64, create a UserDefinedType from the ValuetypeDecl
              receiverType = new UserDefinedType(expr.Origin, vtDecl.Name, vtDecl, ri.TypeArgs);
            } else {
              receiverType = (UserDefinedType)ty.NormalizeExpand();
            }
            var receiver = new StaticReceiverExpr(expr.Lhs.Origin, receiverType, (TopLevelDeclWithMembers)member.EnclosingClass, false) {
              ContainerExpression = expr.Lhs
            };
            receiver.PreType = Type2PreType(receiver.Type);
            r = ResolveExprDotCall(expr.Origin, expr.SuffixNameNode, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
        if (r == null) {
          ReportMemberNotFoundError(expr.Origin, name, null, ri.Decl, resolutionContext);
        }

      } else if (lhs != null) {
        // ----- 4. Look up name in the type of the Lhs
        var (member, tentativeReceiverPreType) = FindMember(expr.Origin, expr.Lhs.PreType, name, resolutionContext,
          expr.Lhs.Resolved != null);
        if (member != null) {
          if (!member.IsStatic) {
            var receiver = expr.Lhs;
            AddSubtypeConstraint(tentativeReceiverPreType, receiver.PreType, expr.Origin,
              $"receiver type ({{1}}) does not have a member named '{name}'");
            r = ResolveExprDotCall(expr.Origin, expr.SuffixNameNode, receiver, tentativeReceiverPreType, member, args, expr.OptTypeArguments,
              resolutionContext, allowMethodCall);
          } else {
            var receiver = new StaticReceiverExpr(expr.Origin, new InferredTypeProxy(), true) {
              PreType = tentativeReceiverPreType.SansPrintablePreType(),
              ObjectToDiscard = lhs
            };
            r = ResolveExprDotCall(expr.Origin, expr.SuffixNameNode, receiver, null, member, args, expr.OptTypeArguments, resolutionContext,
              allowMethodCall);
          }
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .PreType
        expr.PreType = CreatePreTypeProxy("ExprDotName error, so using proxy instead");
      } else {
        resolver.CheckForAmbiguityInShadowedImportedModule(shadowedImport, name, expr.Origin, false, isLastNameSegment);
        expr.ResolvedExpression = r;
        // TODO: do we need something analogous to this for pre-types?  expr.Type = r.Type.UseInternalSynonym();
        expr.PreType = r.PreType;
      }
      return rWithArgs;
    }

    Expression ResolveExprDotCall(IOrigin tok, Name name, Expression receiver, DPreType receiverPreTypeBound/*?*/,
      MemberDecl member, List<ActualBinding> args, List<Type> optTypeArguments, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.PreType.Normalize() is DPreType);
      Contract.Requires(member != null);
      Contract.Requires(resolutionContext != null && resolutionContext != null);

      ResolvePreTypeSignature(member);

      receiverPreTypeBound ??= (DPreType)receiver.PreType.Normalize();

      var rr = new MemberSelectExpr(tok, receiver, name) {
        Member = member
      };

      // Now, fill in rr.PreType.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      rr.PreTypeApplicationAtEnclosingClass = [];
      rr.PreTypeApplicationJustMember = [];
      var rType = receiverPreTypeBound;
      var subst = PreType.PreTypeSubstMap(rType.Decl.TypeArgs, rType.Arguments);
      Contract.Assert(member.EnclosingClass != null);
      rr.PreTypeApplicationAtEnclosingClass.AddRange(rType.AsParentType(member.EnclosingClass, this).Arguments);

      if (member is Field field) {
        if (optTypeArguments != null) {
          ReportError(tok, "a field ({0}) does not take any type arguments (got {1})", field.Name, optTypeArguments.Count);
        }
        subst = BuildPreTypeArgumentSubstitute(subst, receiverPreTypeBound);
        rr.PreType = field.PreType.Substitute(subst);
      } else if (member is Function function) {
        if (function is TwoStateFunction && !resolutionContext.IsTwoState) {
          ReportError(tok, "two-state function ('{0}') can only be called in a two-state context", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null) {
          if (suppliedTypeArguments == function.TypeArgs.Count) {
            // preserve the given types in the resolved MemberSelectExpr
            rr.TypeApplicationJustMember = optTypeArguments;
          } else {
            ReportError(tok, "function '{0}' expects {1} type argument{2} (got {3})",
              member.Name, function.TypeArgs.Count, Util.Plural(function.TypeArgs.Count), suppliedTypeArguments);
          }
        }
        for (int i = 0; i < function.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? Type2PreType(optTypeArguments[i]) :
            CreatePreTypeProxy($"function call to {function.Name}, type argument {i}");
          rr.PreTypeApplicationJustMember.Add(ta);
          subst.Add(function.TypeArgs[i], ta);
        }
        subst = BuildPreTypeArgumentSubstitute(subst, receiverPreTypeBound);
        AddTypeBoundConstraints(tok, function.TypeArgs, subst);
        var inParamTypes = function.Ins.ConvertAll(f => f.PreType.Substitute(subst));
        var resultType = Type2PreType(function.ResultType).Substitute(subst);
        rr.PreType = BuiltInArrowType(inParamTypes, resultType, function.Reads.Expressions.Count != 0, function.Req.Count != 0);
      } else {
        // the member is a method
        var method = (MethodOrConstructor)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given resolutionContext
          ReportError(tok, "expression is not allowed to invoke a {0} ({1})", member.WhatKind, member.Name);
          return null;
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null) {
          if (suppliedTypeArguments == method.TypeArgs.Count) {
            // preserve the given types in the resolved MemberSelectExpr
            rr.TypeApplicationJustMember = optTypeArguments;
          } else {
            ReportError(tok, "method '{0}' expects {1} type argument{2} (got {3})",
              member.Name, method.TypeArgs.Count, Util.Plural(method.TypeArgs.Count), suppliedTypeArguments);
          }
        }
        for (int i = 0; i < method.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? Type2PreType(optTypeArguments[i]) :
            CreatePreTypeProxy($"method call to {method.Name}, type argument {i}");
          rr.PreTypeApplicationJustMember.Add(ta);
          subst.Add(method.TypeArgs[i], ta);
        }
        subst = BuildPreTypeArgumentSubstitute(subst, receiverPreTypeBound);
        AddTypeBoundConstraints(tok, method.TypeArgs, subst);
        rr.PreType = new MethodPreType($"call to {method.WhatKind} {method.Name}");  // fill in this field, in order to make "rr" resolved
      }
      return rr;
    }

    void AddTypeBoundConstraints(IOrigin tok, List<TypeParameter> typeParameters, Dictionary<TypeParameter, PreType> subst) {
      foreach (var typeParameter in typeParameters) {
        foreach (var preTypeBound in TypeParameterBounds2PreTypes(typeParameter)) {
          var preTypeBoundWithSubst = preTypeBound.Substitute(subst);
          var actualPreType = subst[typeParameter];
          AddSubtypeConstraint(preTypeBoundWithSubst, actualPreType, tok,
            $"actual type argument '{{1}}' for formal type parameter '{typeParameter.Name}' must satisfy the type bound '{{0}}'");
        }
      }
    }

    public MethodCallInformation ResolveApplySuffix(ApplySuffix e, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(e != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<MethodCallInformation>() == null || allowMethodCall);

      if (e.MethodCallInfo != null) {
        return e.MethodCallInfo;
      }

      Expression r = null;  // upon success, the expression to which the ApplySuffix resolves
      var errorCount = ErrorCount;
      if (e.Lhs is NameSegment) {
        r = ResolveNameSegment((NameSegment)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else if (e.Lhs is ExprDotName) {
        r = ResolveDotSuffix((ExprDotName)e.Lhs, false, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else {
        ResolveExpression(e.Lhs, resolutionContext);
      }
      if (e.Lhs.PreType == null) {
        // some error had been detected during the attempted resolution of e.Lhs
        e.Lhs.PreType = CreatePreTypeProxy("unresolved ApplySuffix LHS");
      }
      Label atLabel = null;
      if (e.AtTok != null) {
        atLabel = DominatingStatementLabels.Find(e.AtTok.val);
        if (atLabel == null) {
          ReportError(e.AtTok, "no label '{0}' in scope at this time", e.AtTok.val);
        }
      }
      if (r == null) {
        // e.Lhs denotes a function value, or at least it's used as if it were
        var dp = Constraints.FindDefinedPreType(e.Lhs.PreType, false);
        if (dp != null && DPreType.IsArrowType(dp.Decl)) {
          // e.Lhs does denote a function value
          // In the general case, we'll resolve this as an ApplyExpr, but in the more common case of the Lhs
          // naming a function directly, we resolve this as a FunctionCallExpr.
          var mse = e.Lhs is NameSegment or ExprDotName ? e.Lhs.Resolved as MemberSelectExpr : null;
          var callee = mse?.Member as Function;
          if (atLabel != null && !(callee is TwoStateFunction)) {
            ReportError(e.AtTok, "an @-label can only be applied to a two-state function");
            atLabel = null;
          }
          if (callee != null) {
            // resolve as a FunctionCallExpr instead of as an ApplyExpr(MemberSelectExpr)
            var rr = new FunctionCallExpr(e.Origin, mse.MemberNameNode, mse.Obj, e.Origin, e.CloseParen, e.Bindings, atLabel) {
              Function = callee,
              PreTypeApplication_AtEnclosingClass = mse.PreTypeApplicationAtEnclosingClass,
              PreTypeApplication_JustFunction = mse.PreTypeApplicationJustMember,
              TypeApplication_AtEnclosingClass = mse.TypeApplicationAtEnclosingClass,
              TypeApplication_JustFunction = mse.TypeApplicationJustMember
            };
            var typeMap = mse.PreTypeArgumentSubstitutionsAtMemberDeclaration();
            var preTypeMap = BuildPreTypeArgumentSubstitute(
                typeMap.Keys.ToDictionary(tp => tp, tp => typeMap[tp]));
            ResolveActualParameters(rr.Bindings, callee.Ins, e.Origin, callee, resolutionContext, preTypeMap, callee.IsStatic ? null : mse.Obj);
            rr.PreType = Type2PreType(callee.ResultType).Substitute(preTypeMap);
            if (errorCount == ErrorCount) {
              Contract.Assert(!(mse.Obj is StaticReceiverExpr) || callee.IsStatic);  // this should have been checked already
              Contract.Assert(callee.Ins.Count == rr.Args.Count);  // this should have been checked already
            }
            // further bookkeeping
            if (callee is ExtremePredicate extremePredicateCallee) {
              extremePredicateCallee.Uses.Add(rr);
            }
            r = rr;
            ResolveExpression(r, resolutionContext);
          } else {
            // resolve as an ApplyExpr
            var formals = new List<Formal>();
            for (var i = 0; i < dp.Arguments.Count - 1; i++) {
              var argType = dp.Arguments[i];
              var formal = new ImplicitFormal(e.Origin, "_#p" + i, new InferredTypeProxy(), true, false);
              formal.PreType = argType;
              formals.Add(formal);
            }
            ResolveActualParameters(e.Bindings, formals, e.Origin, dp, resolutionContext, new Dictionary<TypeParameter, PreType>(), null);
            r = new ApplyExpr(e.Lhs.Origin, e.Lhs, e.Args, e.CloseParen);
            ResolveExpression(r, resolutionContext);
            r.PreType = dp.Arguments.Last();
          }
        } else {
          // e.Lhs is used as if it were a function value, but it isn't
          var lhs = e.Lhs.Resolved;
          if (lhs is { PreType: PreTypePlaceholderModule }) {
            ReportError(e.Origin, "name of module ({0}) is used as a function", ((ResolverIdentifierExpr)lhs).Decl.Name);
          } else if (lhs is { PreType: PreTypePlaceholderType }) {
            var ri = (ResolverIdentifierExpr)lhs;
            ReportError(e.Origin, "name of {0} ({1}) is used as a function", ri.Decl.WhatKind, ri.Decl.Name);
          } else {
            if (lhs is MemberSelectExpr { Member: MethodOrConstructor } mse) {
              if (atLabel != null) {
                Contract.Assert(mse != null); // assured by the parser
                if (mse.Member is TwoStateLemma) {
                  mse.AtLabel = atLabel;
                } else {
                  ReportError(e.AtTok, "an @-label can only be applied to a two-state lemma");
                }
              }
              if (allowMethodCall) {
                Contract.Assert(!e.Bindings.WasResolved); // we expect that .Bindings has not yet been processed, so we use just .ArgumentBindings in the next lines
                var method = (MethodOrConstructor)mse.Member;
                foreach (var inputParameter in method.Ins) {
                  EnclosingInputParameterFormals.Push(inputParameter.Name, inputParameter);
                }

                EnclosingMethodCall = method;
                foreach (var binding in e.Bindings.ArgumentBindings) {
                  ResolveExpression(binding.Actual, resolutionContext);
                }
                e.MethodCallInfo = new MethodCallInformation(e.Origin, mse, e.Bindings.ArgumentBindings);
                return e.MethodCallInfo;
              } else {
                ReportError(e.Origin, "{0} call is not allowed to be used in an expression resolutionContext ({1})", mse.Member.WhatKind, mse.Member.Name);
              }
            } else if (lhs != null) {  // if e.Lhs.Resolved is null, then e.Lhs was not successfully resolved and an error has already been reported
              ReportError(e.Origin, "non-function expression (of type {0}) is called with parameters", e.Lhs.PreType);
            }
          }
          // resolve the arguments, even in the presence of the errors above
          foreach (var binding in e.Bindings.ArgumentBindings) {
            ResolveExpression(binding.Actual, resolutionContext);
          }
        }
      }
      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .PreType
        e.PreType = CreatePreTypeProxy("unresolved ApplySuffix");
      } else {
        e.ResolvedExpression = r;
        e.PreType = r.PreType;
      }
      return null; // not a method call
    }

    /// <summary>
    /// Attempt to rewrite a datatype update into more primitive operations, after doing the appropriate resolution checks.
    /// Upon success, return that rewritten expression and set "legalSourceConstructors".
    /// Upon some resolution error, report an error and return null (caller should not use "legalSourceConstructors").
    /// Note, "root.PreType" is allowed to be different from "rootPreType"; in particular, "root.PreType" may still be a proxy.
    ///
    /// Actually, the method returns two expressions (or returns "(null, null)"). The first expression is the desugaring to be
    /// used when the DatatypeUpdateExpr is used in a ghost context. The second is to be used for a compiled context. In either
    /// case, "legalSourceConstructors" contains both ghost and compiled constructors.
    ///
    /// The reason for computing both desugarings here is that it's too early to tell if the DatatypeUpdateExpr is being used in
    /// a ghost or compiled context. This is a consequence of doing the deguaring so early. But it's also convenient to do the
    /// desugaring during resolution, because then the desugaring can be constructed as a non-resolved expression on which ResolveExpression
    /// is called--this is easier than constructing an already-resolved expression.
    /// </summary>
    (Expression, Expression) ResolveDatatypeUpdate(IOrigin tok, DPreType rootPreType, Expression root, DatatypeDecl dt,
      List<Tuple<Token, string, Expression>> memberUpdates,
      ResolutionContext resolutionContext, out List<MemberDecl> members, out List<DatatypeCtor> legalSourceConstructors) {
      Contract.Requires(tok != null);
      Contract.Requires(root != null);
      Contract.Requires(rootPreType != null);
      Contract.Requires(dt != null);
      Contract.Requires(memberUpdates != null);
      Contract.Requires(resolutionContext != null);

      legalSourceConstructors = null;
      members = [];
      Contract.Assert(rootPreType.Decl == dt);
      Contract.Assert(rootPreType.Arguments.Count == dt.TypeArgs.Count);

      // First, compute the list of candidate result constructors, that is, the constructors
      // that have all of the mentioned destructors. Issue errors for duplicated names and for
      // names that are not destructors in the datatype.
      var candidateResultCtors = dt.Ctors;  // list of constructors that have all the so-far-mentioned destructors
      var memberNames = new HashSet<string>();
      var rhsBindings = new Dictionary<string, Tuple<BoundVar/*let variable*/, IdentifierExpr/*id expr for let variable*/, Expression /*RHS in given syntax*/>>();
      foreach (var (updateToken, updateName, updateValue) in memberUpdates) {
        if (memberNames.Contains(updateName)) {
          ReportError(updateToken, $"duplicate update member '{updateName}'");
        } else {
          memberNames.Add(updateName);
          if (!resolver.GetClassMembers(dt).TryGetValue(updateName, out var member)) {
            ReportError(updateToken, "member '{0}' does not exist in datatype '{1}'", updateName, dt.Name);
          } else if (member is not DatatypeDestructor) {
            ReportError(updateToken, "member '{0}' is not a destructor in datatype '{1}'", updateName, dt.Name);
          } else {
            members.Add(member);
            var destructor = (DatatypeDestructor)member;
            var intersection = new List<DatatypeCtor>(candidateResultCtors.Intersect(destructor.EnclosingCtors));
            if (intersection.Count == 0) {
              ReportError(updateToken,
                "updated datatype members must belong to the same constructor (unlike the previously mentioned destructors, '{0}' does not belong to {1})",
                updateName, DatatypeDestructor.PrintableCtorNameList(candidateResultCtors, "or"));
            } else {
              candidateResultCtors = intersection;
              if (destructor.IsGhost) {
                rhsBindings.Add(updateName, new Tuple<BoundVar, IdentifierExpr, Expression>(null, null, updateValue));
              } else {
                var xName = resolver.FreshTempVarName($"dt_update#{updateName}#", resolutionContext.CodeContext);
                var xVar = new BoundVar(new AutoGeneratedOrigin(tok), xName, new InferredTypeProxy());
                var x = new IdentifierExpr(new AutoGeneratedOrigin(tok), xVar);
                rhsBindings.Add(updateName, new Tuple<BoundVar, IdentifierExpr, Expression>(xVar, x, updateValue));
              }
            }
          }
        }
      }
      if (candidateResultCtors.Count == 0) {
        return (null, null);
      }

      // Check that every candidate result constructor has given a name to all of its parameters.
      var hasError = false;
      foreach (var ctor in candidateResultCtors) {
        if (ctor.Formals.Exists(f => !f.HasName)) {
          ReportError(tok, $"candidate result constructor '{ctor.Name}' has an anonymous parameter" +
                           " (to use in datatype update expression, name all the parameters of the candidate result constructors)");
          hasError = true;
        }
      }
      if (hasError) {
        return (null, null);
      }

      // The legal source constructors are the candidate result constructors. (Yep, two names for the same thing.)
      legalSourceConstructors = candidateResultCtors;
      Contract.Assert(1 <= legalSourceConstructors.Count);

      var desugaringForGhostContext = DesugarDatatypeUpdate(tok, root, rootPreType, candidateResultCtors, rhsBindings, resolutionContext);
      var nonGhostConstructors = candidateResultCtors.Where(ctor => !ctor.IsGhost).ToList();
      if (nonGhostConstructors.Count == candidateResultCtors.Count) {
        return (desugaringForGhostContext, desugaringForGhostContext);
      }
      var desugaringForCompiledContext = DesugarDatatypeUpdate(tok, root, rootPreType, nonGhostConstructors, rhsBindings, resolutionContext);
      return (desugaringForGhostContext, desugaringForCompiledContext);
    }

    /// <summary>
    /// Rewrite the datatype update root.(x := X, y := Y, ...) into a resolved expression:
    ///     var d := root;
    ///     var x := X;  // EXCEPT: don't do this for ghost fields (see below)
    ///     var y := Y;
    ///     ...
    ///     if d.CandidateResultConstructor0 then
    ///       CandidateResultConstructor0(x, y, ..., d.f0, d.f1, ...)  // for a ghost field x, use the expression X directly
    ///     else if d.CandidateResultConstructor1 then
    ///       CandidateResultConstructor0(x, y, ..., d.g0, d.g1, ...)
    ///     ...
    ///     else
    ///       CandidateResultConstructorN(x, y, ..., d.k0, d.k1, ...)
    ///
    /// </summary>
    private Expression DesugarDatatypeUpdate(IOrigin tok, Expression root, DPreType rootPreType,
      List<DatatypeCtor> candidateResultCtors, Dictionary<string, Tuple<BoundVar, IdentifierExpr, Expression>> rhsBindings,
      ResolutionContext resolutionContext) {

      if (candidateResultCtors.Count == 0) {
        return root;
      }

      // Create a unique name for d', the variable we introduce in the let expression
      var dName = resolver.FreshTempVarName("dt_update_tmp#", resolutionContext.CodeContext);
      var dVar = new BoundVar(new AutoGeneratedOrigin(tok), dName, new InferredTypeProxy()) {
        PreType = rootPreType
      };
      var d = new IdentifierExpr(new AutoGeneratedOrigin(tok), dVar);
      Expression body = null;
      candidateResultCtors.Reverse();
      foreach (var crc in candidateResultCtors) {
        // Build the arguments to the datatype constructor, using the updated value in the appropriate slot
        var actualBindings = new List<ActualBinding>();
        foreach (var f in crc.Formals) {
          Expression ctorArg;
          if (rhsBindings.TryGetValue(f.Name, out var info)) {
            ctorArg = info.Item2 ?? info.Item3;
          } else {
            ctorArg = new ExprDotName(tok, d, new Name(f.Name), null);
          }
          var bindingName = new Token(tok.line, tok.col) {
            Uri = tok.Uri,
            val = f.Name
          };
          actualBindings.Add(new ActualBinding(bindingName, ctorArg));
        }
        var ctorCall = new DatatypeValue(tok, crc.EnclosingDatatype.Name, crc.Name, actualBindings) {
          Ctor = crc
        };
        if (body == null) {
          body = ctorCall;
        } else {
          // body := if d.crc? then ctor_call else body
          var guard = new ExprDotName(tok, d, new Name(crc.QueryField.Name), null);
          body = new ITEExpr(tok, false, guard, ctorCall, body);
        }
      }
      Contract.Assert(body != null); // because there was at least one element in candidateResultCtors

      // Wrap the let bindings around body
      var rewrite = body;
      foreach (var entry in rhsBindings) {
        if (entry.Value.Item1 != null) {
          var lhs = new CasePattern<BoundVar>(tok, entry.Value.Item1);
          rewrite = new LetExpr(tok, [lhs], [entry.Value.Item3], rewrite, true);
        }
      }
      var dVarPat = new CasePattern<BoundVar>(tok, dVar);
      rewrite = new LetExpr(tok, [dVarPat], [root], rewrite, true);
      Contract.Assert(rewrite != null);
      ResolveExpression(rewrite, resolutionContext);
      return rewrite;
    }

    /// <summary>
    /// Resolves the case pattern "pat", figuring out if it denotes a variable or a constructor (or is in error).
    /// The caller is expected to have filled in the .type and .PreType fields of any variable occurring in "pat".
    /// </summary>
    void ResolveCasePattern<VT>(CasePattern<VT> pat, PreType sourcePreType, ResolutionContext resolutionContext) where VT : class, IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(sourcePreType != null);
      Contract.Requires(resolutionContext != null);

      var dtd = (sourcePreType.Normalize() as DPreType)?.Decl as DatatypeDecl;
      List<PreType> sourceTypeArguments = null;
      // Find the constructor in the given datatype
      // If what was parsed was just an identifier, we will interpret it as a datatype constructor, if possible
      DatatypeCtor ctor = null;
      if (dtd != null) {
        sourceTypeArguments = ((DPreType)sourcePreType.Normalize()).Arguments;
        if (pat.Var == null || (pat.Var != null && pat.Var.Type is TypeProxy)) {
          if (dtd.ConstructorsByName.TryGetValue(pat.Id, out ctor)) {
            if (pat.Arguments == null) {
              if (ctor.Formals.Count != 0) {
                // Leave this as a variable
              } else {
                // Convert to a constructor
                pat.MakeAConstructor();
                pat.Ctor = ctor;
                pat.Var = default(VT);
              }
            } else {
              pat.Ctor = ctor;
              pat.Var = default(VT);
            }
          }
        }
      }

      if (pat.Var != null) {
        // this is a simple resolution
        var v = pat.Var;
        if (resolutionContext.IsGhost) {
          v.MakeGhost();
        }
        Contract.Assert(v.PreType != null);
        // Note, the following type constraint checks that the RHS type can be assigned to the new variable on the left. In particular, it
        // does not check that the entire RHS can be assigned to something of the type of the pattern on the left.  For example, consider
        // a type declared as "datatype Atom<T> = MakeAtom(T)", where T is a non-variant type argument.  Suppose the RHS has type Atom<nat>
        // and that the LHS is the pattern MakeAtom(x: int).  This is okay, despite the fact that Atom<nat> is not assignable to Atom<int>.
        // The reason is that the purpose of the pattern on the left is really just to provide a skeleton to introduce bound variables in.
        AddSubtypeConstraint(v.PreType, sourcePreType, v.Origin,
          "type of corresponding source/RHS ({1}) does not match type of bound variable ({0})");
        pat.AssembleExprPreType(null);
        return;
      }

      if (dtd == null) {
        // look up the name of the pattern's constructor
        if (resolver.moduleInfo.Ctors.TryGetValue(pat.Id, out var pair) && !pair.Item2) {
          ctor = pair.Item1;
          pat.Ctor = ctor;
          dtd = ctor.EnclosingDatatype;
          sourceTypeArguments = dtd.TypeArgs.ConvertAll(tp => (PreType)CreatePreTypeProxy($"type parameter '{tp.Name}'"));
          var lhsPreType = new DPreType(dtd, sourceTypeArguments);
          AddSubtypeConstraint(lhsPreType, sourcePreType, pat.Origin, $"type of RHS ({{0}}) does not match type of bound variable '{pat.Id}' ({{1}})");
        }
      }
      if (dtd == null) {
        Contract.Assert(ctor == null);
        ReportError(pat.Origin, "to use a pattern, the type of the source/RHS expression must be a datatype (instead found {0})", sourcePreType);
      } else if (ctor == null) {
        ReportError(pat.Origin, "constructor {0} does not exist in datatype {1}", pat.Id, dtd.Name);
      } else {
        if (pat.Arguments == null) {
          if (ctor.Formals.Count == 0) {
            // The Id matches a constructor of the correct type and 0 arguments,
            // so make it a nullary constructor, not a variable
            pat.MakeAConstructor();
          }
        } else {
          if (ctor.Formals.Count != pat.Arguments.Count) {
            ReportError(pat.Origin, "pattern for constructor {0} has wrong number of formals (found {1}, expected {2})", pat.Id, pat.Arguments.Count, ctor.Formals.Count);
          }
        }
        // build the type-parameter substitution map for this use of the datatype
        Contract.Assert(dtd.TypeArgs.Count == sourceTypeArguments.Count);  // follows from the type previously having been successfully resolved
        var subst = PreType.PreTypeSubstMap(dtd.TypeArgs, sourceTypeArguments);
        // recursively call ResolveCasePattern on each of the arguments
        var prevErrorCount = ErrorCount;
        var j = 0;
        if (pat.Arguments != null) {
          foreach (var arg in pat.Arguments) {
            if (j < ctor.Formals.Count) {
              var formal = ctor.Formals[j];
              var st = formal.PreType.Substitute(subst);
              ResolveCasePattern(arg, st, resolutionContext.WithGhost(resolutionContext.IsGhost || formal.IsGhost));
            }
            j++;
          }
        }
        if (ErrorCount == prevErrorCount && j == ctor.Formals.Count) {
          pat.AssembleExprPreType(sourceTypeArguments);
        }
      }
    }

    /// <summary>
    /// The return value is false iff there is an error in resolving the datatype value.
    /// If there is an error, then an error message is emitted iff complain is true.
    /// </summary>
    private bool ResolveDatatypeValue(ResolutionContext resolutionContext, DatatypeValue dtv, DatatypeDecl datatypeDecl, DPreType ty, bool complain = true) {
      Contract.Requires(resolutionContext != null);
      Contract.Requires(dtv != null);
      Contract.Requires(datatypeDecl != null);
      Contract.Requires(ty == null || (ty.Decl == datatypeDecl && ty.Arguments.Count == datatypeDecl.TypeArgs.Count));

      var ok = true;
      List<PreType> gt;
      if (ty == null) {
        gt = datatypeDecl.TypeArgs.ConvertAll(tp => CreatePreTypeProxy($"datatype type parameter '{tp.Name}'"));
      } else {
        gt = ty.Arguments;
      }
      dtv.InferredPreTypeArgs.AddRange(gt);
      // Construct a resolved type directly, since we know the declaration is datatypeDecl.
      dtv.PreType = new DPreType(datatypeDecl, gt);

      if (!datatypeDecl.ConstructorsByName.TryGetValue(dtv.MemberName, out var ctor)) {
        ok = false;
        if (complain) {
          ReportError(dtv.Origin, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
        }
      } else {
        Contract.Assert(ctor != null); // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
      }
      if (complain && ctor != null) {
        var subst = PreType.PreTypeSubstMap(datatypeDecl.TypeArgs, gt);
        ResolveActualParameters(dtv.Bindings, ctor.Formals, dtv.Origin, ctor, resolutionContext, subst, null);
      } else {
        // still resolve the expressions
        foreach (var binding in dtv.Bindings.ArgumentBindings) {
          ResolveExpression(binding.Actual, resolutionContext);
        }
        dtv.Bindings.AcceptArgumentExpressionsAsExactParameterList();
      }

      return ok && ctor.Formals.Count == dtv.Arguments.Count;
    }

    PreType ResolveSingleSelectionExpr(IOrigin tok, PreType collectionPreType, Expression index) {
      var resultPreType = CreatePreTypeProxy("selection []");
      Constraints.AddGuardedConstraint(() => {
        var sourcePreType = Constraints.ApproximateReceiverType(collectionPreType, null);
        if (sourcePreType != null && AncestorPreType(sourcePreType) is { } ancestorPreType) {
          var familyDeclName = ancestorPreType.Decl.Name;
          switch (familyDeclName) {
            case PreType.TypeNameArray:
            case PreType.TypeNameSeq:
              ConstrainToIntFamilyOrBitvector(index.PreType, index.Origin, "index expression must have an integer or bitvector type (got {0})");
              AddSubtypeConstraint(resultPreType, ancestorPreType.Arguments[0], tok, "type does not agree with element type {1} (got {0})");
              break;
            case PreType.TypeNameMultiset:
              AddSubtypeConstraint(ancestorPreType.Arguments[0], index.PreType, index.Origin, "type does not agree with element type {0} (got {1})");
              ConstrainToIntFamily(resultPreType, tok, "multiset multiplicity must have an integer type (got {0})");
              break;
            case PreType.TypeNameMap:
            case PreType.TypeNameImap:
              AddSubtypeConstraint(ancestorPreType.Arguments[0], index.PreType, index.Origin, "type does not agree with domain type {0} (got {1})");
              AddSubtypeConstraint(resultPreType, ancestorPreType.Arguments[1], tok, "type does not agree with value type of {1} (got {0})");
              break;
            default:
              ReportError(tok, "element selection requires a sequence, array, multiset, or map (got {0})", sourcePreType);
              break;
          }
          return true;
        }
        return false;
      });
      return resultPreType;
    }

    void ResolveRangeSelectionExpr(IOrigin tok, PreType sourceCollectionPreType, Expression expr, Expression e0, Expression e1) {
      var resultElementPreType = CreatePreTypeProxy("index-range selection elements");
      SetupCollectionProducingExpr(PreType.TypeNameSeq, false, "index-range selection", expr, resultElementPreType);

      if (e0 != null) {
        ConstrainToIntFamilyOrBitvector(e0.PreType, e0.Origin,
          "multi-element selection expression must have an integer or bitvector type (got {0})");
      }
      if (e1 != null) {
        ConstrainToIntFamilyOrBitvector(e1.PreType, e1.Origin,
          "multi-element selection expression must have an integer or bitvector type (got {0})");
      }

      // In the expression s[e0..e1], correlate the type of s with the result type.
      //   - If s is a sequence type, then the result must be of the same seq or newtype-seq type, with a co-variant element pre-type
      //   - If s is an array type, then the result is allowed to be any seq or newtype-seq with a co-variant element pre-type
      Constraints.AddGuardedConstraint(() => {
        if (sourceCollectionPreType.NormalizeWrtScope() is DPreType sourcePreType) {
          var familyDeclName = AncestorName(sourcePreType);
          switch (familyDeclName) {
            case PreType.TypeNameSeq:
              AddSubtypeConstraint(expr.PreType, sourceCollectionPreType, tok,
                "resulting sequence ({0}) type does not agree with source sequence type ({1})");
              break;
            case PreType.TypeNameArray:
              AddSubtypeConstraint(resultElementPreType, AncestorPreType(sourcePreType)!.Arguments[0], tok,
                "type does not agree with element type {1} (got {0})");
              break;
            default:
              ReportError(tok, "multi-selection of elements requires a sequence or array (got {0})", sourceCollectionPreType);
              break;
          }
          return true;
        }
        return false;
      });
    }

    /// <summary>
    /// Desugar the elphant-operator expression
    ///     var x: T :- E; Body
    /// into
    ///     var burrito := E;
    ///     if button.IsFailure() then
    ///       burrito.PropagateFailure()
    ///     else
    ///       var x: T := burrito.Extract();
    ///       Body
    /// and desugar the elephant-operator expression
    ///     :- E; Body
    /// into
    ///     var burrito := E;
    ///     if button.IsFailure() then
    ///       burrito.PropagateFailure()
    ///     else
    ///       Body
    /// </summary>
    public Expression DesugarElephantExpr(LetOrFailExpr expr, ResolutionContext resolutionContext) {
      // Using the famous monad/burrito analogy, the following variable denotes the burrito
      var burrito = resolver.FreshTempVarName("valueOrError", resolutionContext.CodeContext);
      var burritoType = new InferredTypeProxy();
      // "var burrito := E;"
      return resolver.LetVarIn(expr.Origin, burrito, burritoType, expr.Rhs,
        // "if burrito.IsFailure()"
        new ITEExpr(expr.Origin, false, resolver.VarDotFunction(expr.Origin, burrito, "IsFailure"),
          // "then burrito.PropagateFailure()"
          resolver.VarDotFunction(expr.Origin, burrito, "PropagateFailure"),
          // "else"
          expr.Lhs == null
            // "Body"
            ? expr.Body
            // "var x: T := burrito.Extract(); Body"
            : resolver.LetPatIn(expr.Origin, expr.Lhs, resolver.VarDotFunction(expr.Origin, burrito, "Extract"), expr.Body)));
    }

    private void EnsureSupportsErrorHandling(IOrigin tok, DPreType burritoPreType, bool expectExtract, ResolutionContext resolutionContext, [CanBeNull] string keyword) {
      Contract.Requires(tok != null);
      Contract.Requires(burritoPreType != null);

      var (memberIsFailure, _) = FindMember(tok, burritoPreType, "IsFailure", resolutionContext);
      var (memberPropagate, _) = FindMember(tok, burritoPreType, "PropagateFailure", resolutionContext);
      var (memberExtract, _) = FindMember(tok, burritoPreType, "Extract", resolutionContext, reportErrorOnMissingMember: expectExtract);

      if (keyword != null) {
        if (memberIsFailure == null || (memberExtract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract
            ? "members IsFailure() and Extract()"
            : "member IsFailure(), but not Extract()";
          ReportError(tok, $"right-hand side of ':- {keyword}', which is of type '{burritoPreType}', must have {requiredMembers}");
        }
      } else {
        if (memberIsFailure == null || memberPropagate == null || (memberExtract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract ? "IsFailure(), PropagateFailure(), and Extract()" : "IsFailure() and PropagateFailure(), but not Extract()";
          ReportError(tok, $"right-hand side of :- operator, which is of type '{burritoPreType}', must have members {requiredMembers}");
        }
      }

      // The following checks are not necessary, because the ghost mismatch is caught later.
      // However, the error messages here are much clearer.
      if (memberIsFailure != null && memberIsFailure.IsGhost) {
        ReportError(tok, $"the IsFailure() member must not be ghost (type {burritoPreType} used in RHS of :- operator)");
      }
      if (keyword == null && memberPropagate != null && memberPropagate.IsGhost) {
        ReportError(tok, $"the PropagateFailure() member must not be ghost (type {burritoPreType} used in RHS of :- operator)");
      }
    }

    private bool TryApplyFp64ArithmeticConstraints(Expression e0, Expression e1, IOrigin tok, ref PreType resultPreType) {
      var e0Normalized = e0.PreType.Normalize();
      var e1Normalized = e1.PreType.Normalize();

      var e0IsFp64 = e0Normalized is DPreType { Decl.Name: PreType.TypeNameFp64 };
      var e1IsFp64 = e1Normalized is DPreType { Decl.Name: PreType.TypeNameFp64 };

      if (!e0IsFp64 && !e1IsFp64) {
        return false;
      }

      var fp64Type = new DPreType(BuiltInTypeDecl(PreType.TypeNameFp64), []);
      resultPreType = fp64Type;
      Constraints.AddEqualityConstraint(e0.PreType, fp64Type, tok, "fp64 arithmetic requires both operands to be fp64");
      Constraints.AddEqualityConstraint(e1.PreType, fp64Type, tok, "fp64 arithmetic requires both operands to be fp64");
      return true;
    }

  }
}
