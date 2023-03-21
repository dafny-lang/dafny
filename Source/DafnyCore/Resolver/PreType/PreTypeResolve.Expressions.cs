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
using Microsoft.Boogie;
using ResolutionContext = Microsoft.Dafny.ResolutionContext;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {
    // ---------------------------------------- Expressions ----------------------------------------

    void ResolveExpression(Expression expr, ResolutionContext resolutionContext) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

      if (expr.PreType != null) {
        // expression has already been pre-resolved
        return;
      }

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.ResolvedExpression = e.E;
        e.PreType = e.E.PreType;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.ResolvedExpression = e.E;
        e.PreType = e.E.PreType;

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.PreType = e.E.PreType;
        AddConfirmation("NumericOrBitvector", e.E.PreType, e.E.tok, "type of unary - must be of a numeric or bitvector type (instead got {0})");
        // Note, e.ResolvedExpression will be filled in during CheckTypeInference, at which time e.PreType has been determined

      } else if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr eStatic) {
          resolver.ResolveType(eStatic.tok, eStatic.UnresolvedType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          eStatic.PreType = Type2PreType(eStatic.UnresolvedType, "static receiver type");
        } else {
          if (e.Value == null) {
            e.PreType = CreatePreTypeProxy("literal 'null'");
            AddDefaultAdvice(e.PreType, AdviceTarget.Object);
            AddConfirmation("IsNullableRefType", e.PreType, e.tok, "type of 'null' is a reference type, but it is used as {0}");
          } else if (e.Value is BigInteger) {
            e.PreType = CreatePreTypeProxy($"integer literal '{e.Value}'");
            AddDefaultAdvice(e.PreType, AdviceTarget.Int);
            AddConfirmation("IntOrBitvectorOrORDINAL", e.PreType, e.tok, "integer literal used as if it had type {0}");
          } else if (e.Value is BaseTypes.BigDec) {
            e.PreType = CreatePreTypeProxy($"real literal '{e.Value}'");
            AddDefaultAdvice(e.PreType, AdviceTarget.Real);
            AddConfirmation("InRealFamily", e.PreType, e.tok, "type of real literal is used as {0}"); // TODO: make this error message have the same form as the one for integers above
          } else if (e.Value is bool) {
            e.PreType = CreatePreTypeProxy($"boolean literal '{e.Value.ToString().ToLower()}'");
            AddDefaultAdvice(e.PreType, AdviceTarget.Bool);
            AddConfirmation("InBoolFamily", e.PreType, e.tok, "boolean literal used as if it had type {0}");
          } else if (e is CharLiteralExpr) {
            e.PreType = CreatePreTypeProxy($"character literal '{e.Value}'");
            AddDefaultAdvice(e.PreType, AdviceTarget.Char);
            AddConfirmation("InCharFamily", e.PreType, e.tok, "character literal used as if it had type {0}");
          } else if (e is StringLiteralExpr) {
            e.PreType = CreatePreTypeProxy($"string literal \"{e.Value}\"");
            AddDefaultAdvice(e.PreType, AdviceTarget.String);
            AddConfirmation("InSeqFamily", e.PreType, e.tok, "string literal used as if it had type {0}");
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal type
          }
        }

      } else if (expr is ThisExpr) {
        if (!scope.AllowInstance) {
          ReportError(expr, "'this' is not allowed in a 'static' resolutionContext");
        }
        if (currentClass is ClassDecl cd && cd.IsDefaultClass) {
          // there's no type
        } else {
          var ty = Resolver.GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
          expr.PreType = Type2PreType(ty, "type of 'this'");
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        e.Var = scope.Find(e.Name);
        if (e.Var != null) {
          expr.PreType = e.Var.PreType;
        } else {
          ReportError(expr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
        }

      } else if (expr is DatatypeValue) {
        var dtv = (DatatypeValue)expr;
        if (!resolver.moduleInfo.TopLevels.TryGetValue(dtv.DatatypeName, out var decl)) {
          ReportError(expr.tok, "Undeclared datatype: {0}", dtv.DatatypeName);
        } else if (decl is Resolver.AmbiguousTopLevelDecl) {
          var ad = (Resolver.AmbiguousTopLevelDecl)decl;
          ReportError(expr.tok,
            "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)",
            dtv.DatatypeName, ad.ModuleNames());
        } else if (decl is DatatypeDecl dtd) {
          ResolveDatatypeValue(resolutionContext, dtv, dtd, null);
        } else {
          ReportError(expr.tok, "Expected datatype: {0}", dtv.DatatypeName);
        }

      } else if (expr is DisplayExpression) {
        var e = (DisplayExpression)expr;
        var elementPreType = CreatePreTypeProxy("display expression element type");
        foreach (var ee in e.Elements) {
          ResolveExpression(ee, resolutionContext);
          AddSubtypeConstraint(elementPreType, ee.PreType, ee.tok,
            "All elements of display must have some common supertype (got {1}, but needed type or type of previous elements is {0})");
        }
        var argTypes = new List<PreType>() { elementPreType };
        if (expr is SetDisplayExpr setDisplayExpr) {
          expr.PreType = new DPreType(BuiltInTypeDecl(setDisplayExpr.Finite ? "set" : "iset"), argTypes);
        } else if (expr is MultiSetDisplayExpr) {
          expr.PreType = new DPreType(BuiltInTypeDecl("multiset"), argTypes);
        } else {
          expr.PreType = new DPreType(BuiltInTypeDecl("seq"), argTypes);
        }

      } else if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        var domainPreType = CreatePreTypeProxy("map display expression domain type");
        var rangePreType = CreatePreTypeProxy("map display expression range type");
        foreach (ExpressionPair p in e.Elements) {
          ResolveExpression(p.A, resolutionContext);
          AddSubtypeConstraint(domainPreType, p.A.PreType, p.A.tok,
            "All elements of display must have some common supertype (got {1}, but needed type or type of previous elements is {0})");
          ResolveExpression(p.B, resolutionContext);
          AddSubtypeConstraint(rangePreType, p.B.PreType, p.B.tok,
            "All elements of display must have some common supertype (got {1}, but needed type or type of previous elements is {0})");
        }
        var argTypes = new List<PreType>() { domainPreType, rangePreType };
        expr.PreType = new DPreType(BuiltInTypeDecl(e.Finite ? "map" : "imap"), argTypes);

      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        ResolveNameSegment(e, true, null, resolutionContext, false);

        if (e.PreType is PreTypePlaceholderModule) {
          ReportError(e.tok, "name of module ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment(); // the rest of type checking assumes actual types
        } else if (e.PreType is PreTypePlaceholderType) {
          ReportError(e.tok, "name of type ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment(); // the rest of type checking assumes actual types
        }

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        ResolveDotSuffix(e, true, null, resolutionContext, false);
        if (e.PreType is PreTypePlaceholderModule) {
          ReportError(e.tok, "name of module ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.PreType is PreTypePlaceholderType) {
          ReportError(e.tok, "name of type ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ApplySuffix applySuffix) {
        ResolveApplySuffix(applySuffix, resolutionContext, false);

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        Contract.Assert(false); // this case is always handled by ResolveExprDotCall
#if PROBABLY_NEVER
        ResolveExpression(e.Obj, resolutionContext);
        var (member, tentativeReceiverType) = FindMember(expr.tok, e.Obj.PreType, e.MemberName);
        if (member == null) {
          // error has already been reported by FindMember
        } else if (member is Function fn) {
          e.Member = fn;
          if (fn is TwoStateFunction && !resolutionContext.twoState) {
            ReportError(e.tok, "a two-state function can be used only in a two-state resolutionContext");
          }
          // build the type substitution map
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          Dictionary<TypeParameter, Type> subst;
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            subst = new Dictionary<TypeParameter, Type>();
          } else {
            subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
          }
          foreach (var tp in fn.TypeArgs) {
            Type prox = new InferredTypeProxy();
            subst[tp] = prox;
            e.TypeApplication_JustMember.Add(prox);
          }
          subst = BuildTypeArgumentSubstitute(subst);
          e.Type = SelectAppropriateArrowType(fn.tok, fn.Formals.ConvertAll(f => SubstType(f.Type, subst)), SubstType(fn.ResultType, subst),
            fn.Reads.Count != 0, fn.Req.Count != 0);
          AddCallGraphEdge(resolutionContext, fn, e, false);
        } else if (member is Field field) {
          e.Member = field;
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          if (e.Obj is StaticReceiverExpr && !field.IsStatic) {
            ReportError(expr, "a field must be selected via an object, not just a class name");
          }
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            e.Type = field.Type;
          } else {
            Contract.Assert(ctype.ResolvedClass != null); // follows from postcondition of ResolveMember
            // build the type substitution map
            var subst = TypeSubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            e.Type = SubstType(field.Type, subst);
          }
          AddCallGraphEdgeForField(resolutionContext, field, e);
        } else {
          ReportError(expr, "member {0} in type {1} does not refer to a field or a function", e.MemberName, tentativeReceiverType);
        }
#endif

      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;

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
          e.PreType = ResolveSingleSelectionExpr(e.tok, e.Seq.PreType, e.E0);
        } else {
          e.PreType = ResolveRangeSelectionExpr(e.tok, e.Seq.PreType, e.E0, e.E1);
        }

      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, resolutionContext);
        var elementPreType = CreatePreTypeProxy("multi-dim array select");
        var arrayPreType = BuiltInArrayType(e.Indices.Count, elementPreType);
        AddSubtypeConstraint(arrayPreType, e.Array.PreType, e.Array.tok, "array selection requires an {0} (got {1})");
        int i = 0;
        foreach (var indexExpression in e.Indices) {
          ResolveExpression(indexExpression, resolutionContext);
          ConstrainToIntFamily(indexExpression.PreType, indexExpression.tok,
            "array selection requires integer- or bitvector-based numeric indices (got {0} for index " + i + ")");
          i++;
        }
        e.PreType = elementPreType;

      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, resolutionContext);
        ResolveExpression(e.Index, resolutionContext);
        ResolveExpression(e.Value, resolutionContext);
        AddGuardedConstraint(() => {
          var sourcePreType = e.Seq.PreType.Normalize() as DPreType;
          var ancestorDecl = AncestorDecl(sourcePreType.Decl);
          var familyDeclName = AncestorName(sourcePreType);
          if (familyDeclName == "seq") {
            var elementPreType = sourcePreType.Arguments[0];
            ConstrainToIntFamily(e.Index.PreType, e.Index.tok, "sequence update requires integer- or bitvector-based index (got {0})");
            AddSubtypeConstraint(elementPreType, e.Value.PreType, e.Value.tok,
              "sequence update requires the value to have the element type of the sequence (got {0})");
            return true;
          } else if (familyDeclName == "map" || familyDeclName == "imap") {
            var domainPreType = sourcePreType.Arguments[0];
            var rangePreType = sourcePreType.Arguments[1];
            AddSubtypeConstraint(domainPreType, e.Index.PreType, e.Index.tok,
              familyDeclName + " update requires domain element to be of type {0} (got {1})");
            AddSubtypeConstraint(rangePreType, e.Value.PreType, e.Value.tok,
              familyDeclName + " update requires the value to have the range type {0} (got {1})");
            return true;
          } else if (familyDeclName == "multiset") {
            var elementPreType = sourcePreType.Arguments[0];
            AddSubtypeConstraint(elementPreType, e.Index.PreType, e.Index.tok,
              "multiset update requires domain element to be of type {0} (got {1})");
            ConstrainToIntFamily(e.Value.PreType, e.Value.tok, "multiset update requires integer-based numeric value (got {0})");
            return true;
          } else if (familyDeclName != null) {
            ReportError(expr.tok, "update requires a sequence, map, or multiset (got {0})", e.Seq.PreType);
            return true;
          }
          return false;
        });
        expr.PreType = e.Seq.PreType;

      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        ResolveExpression(e.Root, resolutionContext);
        expr.PreType = CreatePreTypeProxy("datatype update");
        AddGuardedConstraint(() => {
          var (_, memberName, _) = e.Updates[0];
          var (_, tentativeRootPreType) = FindMember(expr.tok, e.Root.PreType, memberName);
          if (tentativeRootPreType != null) {
            if (tentativeRootPreType.Decl is DatatypeDecl datatypeDecl) {
              var let = ResolveDatatypeUpdate(expr.tok, tentativeRootPreType, e.Root, datatypeDecl, e.Updates, resolutionContext, out var legalSourceConstructors);
              // if 'let' returns as 'null', an error has already been reported
              if (let != null) {
                e.ResolvedExpression = let;
                e.LegalSourceConstructors = legalSourceConstructors;
                AddEqualityConstraint(expr.PreType, let.PreType, expr.tok,
                  "result of datatype update expression of type '{1}' is used as if it were of type '{0}'");
              }
            } else {
              ReportError(expr, "datatype update expression requires a root expression of a datatype (got {0})", tentativeRootPreType);
            }
            return true;
          }
          return false;
        });

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        Contract.Assert(false); // this case is always handled by ResolveExprDotCall
#if PROBABLY_NEVER
        ResolveFunctionCallExpr(e, resolutionContext);
#endif

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        ResolveExpression(e.Function, resolutionContext);
        foreach (var arg in e.Args) {
          ResolveExpression(arg, resolutionContext);
        }
        expr.PreType = CreatePreTypeProxy("apply expression result");

        AddGuardedConstraint(() => {
          if (e.Function.PreType.Normalize() is DPreType dp) {
            if (!DPreType.IsArrowType(dp.Decl)) {
              ReportError(e.tok, "non-function expression (of type {0}) is called with parameters", e.Function.PreType);
            } else {
              var arity = dp.Decl.TypeArgs.Count - 1;
              if (arity != e.Args.Count) {
                ReportError(e.tok,
                  "wrong number of arguments to function application (function type '{0}' expects {1}, got {2})", e.Function.PreType,
                  arity, e.Args.Count);
              } else {
                for (var i = 0; i < arity; i++) {
                  AddSubtypeConstraint(dp.Arguments[i], e.Args[i].PreType, e.Args[i].tok,
                    "type mismatch for argument" + (arity == 1 ? "" : " " + i) + " (function expects {0}, got {1})");
                }
                AddSubtypeConstraint(expr.PreType, dp.Arguments[arity], expr.tok, "function result '{1}' used as if it had type '{0}'");
              }
            }
            return true;
          }
          return false;
        });

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var elementType = e.ExplicitElementType ?? new InferredTypeProxy();
        resolver.ResolveType(e.tok, elementType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        var elementPreType = Type2PreType(elementType);
        ResolveExpression(e.N, resolutionContext);
        ConstrainToIntFamily(e.N.PreType, e.N.tok, "sequence construction must use an integer-based expression for the sequence size (got {0})");
        ResolveExpression(e.Initializer, resolutionContext);
        var intPreType = Type2PreType(resolver.builtIns.Nat());
        var arrowPreType = new DPreType(BuiltInArrowTypeDecl(1), new List<PreType>() { intPreType, elementPreType });
        var resultPreType = new DPreType(BuiltInTypeDecl("seq"), new List<PreType>() { elementPreType });
        AddSubtypeConstraint(arrowPreType, e.Initializer.PreType, e.Initializer.tok,
          () => {
            var strFormat = "sequence-construction initializer expression expected to have type '{0}' (instead got '{1}')";
            if (PreType.Same(elementPreType, e.Initializer.PreType)) {
              var hintString = " (perhaps write '_ =>' in front of the expression you gave in order to make it an arrow type)";
              strFormat += hintString;
            }
            return strFormat;
          });
        expr.PreType = resultPreType;

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var targetElementPreType = CreatePreTypeProxy("multiset conversion element type");
        AddGuardedConstraint(() => {
          if (e.E.PreType.Normalize() is DPreType dp) {
            if (dp.Decl.Name == "set" || dp.Decl.Name == "seq") {
              Contract.Assert(dp.Arguments.Count == 1);
              var sourceElementPreType = dp.Arguments[0];
              AddSubtypeConstraint(targetElementPreType, sourceElementPreType, e.E.tok, "expecting element type {0} (got {1})");
            } else {
              ReportError(e.E.tok, "can only form a multiset from a seq or set (got {0})", e.E.PreType);
            }
            return true;
          }
          return false;
        });
        expr.PreType = new DPreType(BuiltInTypeDecl("multiset"), new List<PreType>() { targetElementPreType });

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        e.AtLabel = resolver.ResolveDominatingLabelInExpr(expr.tok, e.At, "old", resolutionContext);
        ResolveExpression(e.E, new ResolutionContext(resolutionContext.CodeContext, false) with { InOld = true });
        expr.PreType = e.E.PreType;

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        e.AtLabel = resolver.ResolveDominatingLabelInExpr(expr.tok, e.At, "unchanged", resolutionContext);
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, FrameExpressionUse.Unchanged, resolutionContext.CodeContext);
        }
        ConstrainTypeExprBool(e, "result of 'unchanged' is boolean, but is used as if it had type {0}");

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        e.AtLabel = resolver.ResolveDominatingLabelInExpr(expr.tok, e.At, "fresh", resolutionContext);
        // the type of e.E must be either an object or a set/seq of objects
        AddConfirmation("Freshable", e.E.PreType, e.E.tok, "the argument of a fresh expression must denote an object or a set or sequence of objects (instead got {0})");
        ConstrainTypeExprBool(e, "result of 'fresh' is boolean, but is used as if it had type {0}");

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            AddConfirmation("BooleanBits", e.E.PreType, expr.tok, "logical/bitwise negation expects a boolean or bitvector argument (instead got {0})");
            expr.PreType = e.E.PreType;
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            AddConfirmation("Sizeable", e.E.PreType, expr.tok, "size operator expects a collection argument (instead got {0})");
            expr.PreType = CreatePreTypeProxy("cardinality");
            ConstrainToIntFamily(expr.PreType, expr.tok, "integer literal used as if it had type {0}");
            break;
          case UnaryOpExpr.Opcode.Allocated:
            // the argument is allowed to have any type at all
            expr.PreType = ConstrainResultToBoolFamily(expr.tok, "allocated", "boolean literal used as if it had type {0}");
            if (2 <= resolver.Options.Allocated &&
                ((resolutionContext.CodeContext is Function && !resolutionContext.InOld) || resolutionContext.CodeContext is ConstantField || CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl)) {
              var declKind = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl redir ? redir.WhatKind : ((MemberDecl)resolutionContext.CodeContext).WhatKind;
              ReportError(expr, "a {0} definition is not allowed to depend on the set of allocated references", declKind);
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var prevErrorCount = ErrorCount;
        resolver.ResolveType(e.tok, e.ToType, resolutionContext, new Resolver.ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        if (ErrorCount == prevErrorCount) {
          var toPreType = (DPreType)Type2PreType(e.ToType);
          var ancestorDecl = AncestorDecl(toPreType.Decl);
          var familyDeclName = ancestorDecl.Name;
          if (familyDeclName == "int") {
            AddConfirmation("NumericOrBitvectorOrCharOrORDINAL", e.E.PreType, expr.tok, "type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (familyDeclName == "real") {
            AddConfirmation("NumericOrBitvectorOrCharOrORDINAL", e.E.PreType, expr.tok, "type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (IsBitvectorName(familyDeclName)) {
            AddConfirmation("NumericOrBitvectorOrCharOrORDINAL", e.E.PreType, expr.tok, "type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (familyDeclName == "char") {
            AddConfirmation("NumericOrBitvectorOrCharOrORDINAL", e.E.PreType, expr.tok, "type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (familyDeclName == "ORDINAL") {
            AddConfirmation("NumericOrBitvectorOrCharOrORDINAL", e.E.PreType, expr.tok, "type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (DPreType.IsReferenceTypeDecl(ancestorDecl)) {
            AddComparableConstraint(toPreType, e.E.PreType, expr.tok, "type cast to reference type '{0}' must be from an expression assignable to it (got '{1}')");
          } else {
            ReportError(expr, "type conversions are not supported to this type (got {0})", e.ToType);
          }
          e.PreType = toPreType;
        } else {
          e.PreType = CreatePreTypeProxy("'as' target type");
        }

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        expr.PreType = ConstrainResultToBoolFamilyOperator(expr.tok, "is");
        resolver.ResolveType(e.tok, e.ToType, resolutionContext, new Resolver.ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        var toPreType = Type2PreType(e.ToType);
        AddComparableConstraint(toPreType, e.E.PreType, expr.tok, "type test for type '{0}' must be from an expression assignable to it (got '{1}')");
        AddConfirmation(() => {
          // TODO: all of these tests should be revisited (they don't seem right in the presence of newtype's)
          var fromPT = e.E.PreType.Normalize() as DPreType;
          var toPT = toPreType.Normalize() as DPreType;
          if (fromPT != null && toPT != null && IsSuperPreTypeOf(toPT, fromPT)) {
            // This test is allowed and it always returns true
          } else if (fromPT == null || toPT == null || !IsSuperPreTypeOf(fromPT, toPT)) {
            // TODO: I think this line can never be reached, since we get here only if we get past the guarded Comparable constraint
            ReportError(e.tok, "a type test to '{0}' must be from a compatible type (got '{1}')", toPreType, e.E.PreType);
          } else if (!DPreType.IsReferenceTypeDecl(toPT.Decl)) {
            ReportError(e.tok, "a non-trivial type test is allowed only for reference types (tried to test if '{1}' is a '{0}')", toPreType, e.E.PreType);
          }
        });

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        ResolveExpression(e.E0, resolutionContext);
        ResolveExpression(e.E1, resolutionContext);
        expr.PreType = ResolveBinaryExpr(e.tok, e.Op, e.E0, e.E1, resolutionContext);

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        ResolveExpression(e.E0, resolutionContext);
        ResolveExpression(e.E1, resolutionContext);
        ResolveExpression(e.E2, resolutionContext);
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            expr.PreType = ConstrainResultToBoolFamily(expr.tok, "ternary op", "boolean literal used as if it had type {0}");
            AddConfirmation("IntOrORDINAL", e.E0.PreType, expr.tok, "prefix-equality limit argument must be an ORDINAL or integer expression (got {0})");
            AddComparableConstraint(e.E1.PreType, e.E2.PreType, expr.tok, "arguments must have the same type (got {0} and {1})");
            AddConfirmation("IsCoDatatype", e.E1.PreType, expr.tok, "arguments to prefix equality must be codatatypes (instead of {0})");
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var bv in e.BoundVars) {
            int prevErrorCount = ErrorCount;
            resolver.ResolveType(bv.Tok, bv.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            bv.PreType = Type2PreType(bv.Type);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, resolutionContext);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            ReportError(expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
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
              ReportError(lhs.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
            }
            i++;
          }
        } else {
          // let-such-that expression
          if (e.RHSs.Count != 1) {
            ReportError(expr, "let-such-that expression must have just one RHS (found {0})", e.RHSs.Count);
          }
          // the bound variables are in scope in the RHS of a let-such-that expression
          scope.PushMarker();
          foreach (var lhs in e.LHSs) {
            Contract.Assert(lhs.Var != null);  // the parser already checked that every LHS is a BoundVar, not a general pattern
            var v = lhs.Var;
            resolver.ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            ScopePushAndReport(v, "let-variable", true);
            lhs.AssembleExprPreType(null);
#if SOON
            resolver.AddTypeDependencyEdges(resolutionContext, v.Type);
#endif
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, resolutionContext);
            rhs.PreType = ConstrainResultToBoolFamily(rhs.tok, "such-that constraint", "type of RHS of let-such-that expression must be boolean (got {0})");
          }
        }
        ResolveExpression(e.Body, resolutionContext);
        ResolveAttributes(e, resolutionContext, false);
        scope.PopMarker();
        expr.PreType = e.Body.PreType;

      } else if (expr is LetOrFailExpr) {
        var e = (LetOrFailExpr)expr;
        e.ResolvedExpression = DesugarElephantExpr(e, resolutionContext);
        e.PreType = e.ResolvedExpression.PreType;
        AddGuardedConstraint(() => {
          if (e.Rhs.PreType.Normalize() is DPreType receiverPreType) {
            bool expectExtract = e.Lhs != null;
            EnsureSupportsErrorHandling(e.tok, receiverPreType, expectExtract);
            return true;
          }
          return false;
        });

      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        if (resolutionContext.CodeContext is Function enclosingFunction) {
          enclosingFunction.ContainsQuantifier = true;
        }
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        scope.PushMarker();
        foreach (var v in e.BoundVars) {
          resolver.ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
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
        expr.PreType = ConstrainResultToBoolFamilyOperator(expr.tok, e.WhatKind);

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        scope.PushMarker();
        foreach (var v in e.BoundVars) {
          resolver.ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          ScopePushAndReport(v, "bound-variable", true);
        }
        ResolveExpression(e.Range, resolutionContext);
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        ResolveExpression(e.Term, resolutionContext);

        ResolveAttributes(e, resolutionContext, false);
        scope.PopMarker();
        expr.PreType = new DPreType(BuiltInTypeDecl(e.Finite ? "set" : "iset"), new List<PreType>() { e.Term.PreType });

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        scope.PushMarker();
        Contract.Assert(e.BoundVars.Count == 1 || (1 < e.BoundVars.Count && e.TermLeft != null));
        foreach (BoundVar v in e.BoundVars) {
          resolver.ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          ScopePushAndReport(v, "bound-variable", true);
          if (v.Type is InferredTypeProxy inferredProxy) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, resolutionContext);
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        if (e.TermLeft != null) {
          ResolveExpression(e.TermLeft, resolutionContext);
        }
        ResolveExpression(e.Term, resolutionContext);

        ResolveAttributes(e, resolutionContext, false);
        scope.PopMarker();
        expr.PreType = new DPreType(BuiltInTypeDecl(e.Finite ? "map" : "imap"),
          new List<PreType>() { e.TermLeft != null ? e.TermLeft.PreType : e.BoundVars[0].PreType, e.Term.PreType });

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        scope.PushMarker();
        foreach (var v in e.BoundVars) {
          resolver.ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          ScopePushAndReport(v, "bound-variable", true);
        }

        if (e.Range != null) {
          ResolveExpression(e.Range, resolutionContext);
          ConstrainTypeExprBool(e.Range, "precondition must be boolean (got {0})");
        }
        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, FrameExpressionUse.Reads, resolutionContext.CodeContext);
        }
        ResolveExpression(e.Term, resolutionContext);
        scope.PopMarker();
        expr.PreType = BuiltInArrowType(e.BoundVars.ConvertAll(v => v.PreType), e.Body.PreType);

      } else if (expr is WildcardExpr) {
        var obj = new DPreType(BuiltInTypeDecl("object?"), new List<PreType>() {});
        expr.PreType = new DPreType(BuiltInTypeDecl("set"), new List<PreType>() { obj });

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = ErrorCount;
        ResolveStatement(e.S, resolutionContext);
        if (ErrorCount == prevErrorCount) {
          if (e.S is UpdateStmt updateStmt && updateStmt.ResolvedStatements.Count == 1) {
            var call = (CallStmt)updateStmt.ResolvedStatements[0];
            if (call.Method is TwoStateLemma && !resolutionContext.IsTwoState) {
              ReportError(call, "two-state lemmas can only be used in two-state contexts");
            }
          }
        }
        ResolveExpression(e.E, resolutionContext);
        expr.PreType = e.E.PreType;

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        ResolveExpression(e.Test, resolutionContext);
        ResolveExpression(e.Thn, resolutionContext);
        ResolveExpression(e.Els, resolutionContext);
        e.Test.PreType = ConstrainResultToBoolFamily(e.Test.tok, "if-then-else test", "guard condition in if-then-else expression must be a boolean (instead got {0})");
        expr.PreType = CreatePreTypeProxy("if-then-else branches");
        AddSubtypeConstraint(expr.PreType, e.Thn.PreType, expr.tok, "the two branches of an if-then-else expression must have the same type (got {0} and {1})");
        AddSubtypeConstraint(expr.PreType, e.Els.PreType, expr.tok, "the two branches of an if-then-else expression must have the same type (got {0} and {1})");

#if SOON
      } else if (expr is MatchExpr) {
        ResolveMatchExpr((MatchExpr)expr, resolutionContext);
#endif

      } else if (expr is NestedMatchExpr) {
#if SOON
        var e = (NestedMatchExpr)expr;
        ResolveNestedMatchExpr(e, resolutionContext);
        if (e.ResolvedExpression != null) {
          expr.PreType = e.ResolvedExpression.PreType;
        }
#endif

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.PreType == null) {
        // some resolution error occurred
        expr.PreType = CreatePreTypeProxy("ResolveExpression didn't compute this pre-type");
      }
    }

    private PreType ResolveBinaryExpr(IToken tok, BinaryExpr.Opcode opcode, Expression e0, Expression e1, ResolutionContext resolutionContext) {
      var opString = BinaryExpr.OpcodeString(opcode);
      PreType resultPreType;
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
          AddComparableConstraint(e0.PreType, e1.PreType, tok, "arguments must have comparable types (got {0} and {1})");
          break;

        case BinaryExpr.Opcode.Disjoint:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, null);
          AddConfirmation("Disjointable", e0.PreType, tok, "arguments must be of a set or multiset type (got {0})");
          break;

        case BinaryExpr.Opcode.Lt:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          AddGuardedConstraint(() => {
            var left = e0.PreType.Normalize() as DPreType;
            var right = e1.PreType.Normalize() as DPreType;
            if (left != null && (left.Decl is IndDatatypeDecl || left.Decl is TypeParameter)) {
              AddConfirmation("RankOrderable", e1.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {e0.PreType} and {{0}})");
              return true;
            } else if (right != null && right.Decl is IndDatatypeDecl) {
              AddConfirmation("RankOrderableOrTypeParameter", e0.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {{0}} and {e1.PreType})");
              return true;
            } else if (left != null || right != null) {
              var commonSupertype = CreatePreTypeProxy("common supertype of < operands");
              ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, commonSupertype);
              AddConfirmation("Orderable_Lt", e0.PreType, tok,
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
          AddConfirmation("Orderable_Lt", e0.PreType, tok,
            "arguments to " + opString +
            " must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0})");
          break;

        case BinaryExpr.Opcode.Gt:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          AddGuardedConstraint(() => {
            var left = e0.PreType.Normalize() as DPreType;
            var right = e1.PreType.Normalize() as DPreType;
            if (left != null && left.Decl is IndDatatypeDecl) {
              AddConfirmation("RankOrderableOrTypeParameter", e1.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {e0.PreType} and {{0}})");
              return true;
            } else if (right != null && (right.Decl is IndDatatypeDecl || right.Decl is TypeParameter)) {
              AddConfirmation("RankOrderable", e0.PreType, tok,
                $"arguments to rank comparison must be datatypes (got {{0}} and {e1.PreType})");
              return true;
            } else if (left != null || right != null) {
              var commonSupertype = CreatePreTypeProxy("common supertype of < operands");
              ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, commonSupertype);
              AddConfirmation("Orderable_Gt", e0.PreType, tok,
                "arguments to " + opString + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0})");
              return true;
            }
            return false;
          });
          break;

        case BinaryExpr.Opcode.Ge:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, opString);
          ConstrainToCommonSupertype(tok, opString, e0.PreType, e1.PreType, null);
          AddConfirmation("Orderable_Gt", e0.PreType, tok,
            "arguments to " + opString + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0} and {1})");
          break;

        case BinaryExpr.Opcode.Add:
          resultPreType = CreatePreTypeProxy("result of +");
          AddConfirmation("Plussable", resultPreType, tok,
            "type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like or map-like type (instead got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.Sub:
          resultPreType = CreatePreTypeProxy("result of -");
          AddGuardedConstraint(() => {
            // The following cases are allowed:
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
            var left = a0.Normalize() as DPreType;
            var right = a1.Normalize() as DPreType;
            var familyDeclNameLeft = AncestorName(a0);
            var familyDeclNameRight = AncestorName(a1);
            if (familyDeclNameLeft == "map" || familyDeclNameLeft == "imap") {
              Contract.Assert(left.Arguments.Count == 2);
              var st = new DPreType(BuiltInTypeDecl("set"), new List<PreType>() { left.Arguments[0] });
              DebugPrint($"    DEBUG: guard applies: Minusable {a0} {a1}, converting to {st} :> {a1}");
              AddSubtypeConstraint(st, a1, tok,
                "map subtraction expects right-hand operand to have type {0} (instead got {1})");
              return true;
            } else if (familyDeclNameLeft != null || (familyDeclNameRight != null && familyDeclNameRight != "set")) {
              DebugPrint($"    DEBUG: guard applies: Minusable {a0} {a1}, converting to {a0} :> {a1}");
              AddSubtypeConstraint(a0, a1, tok,
                "type of right argument to - ({0}) must agree with the result type ({1})");
              return true;
            }
            return false;
          });
          ConstrainOperandTypes(tok, opString, e0, null, resultPreType);
          break;

        case BinaryExpr.Opcode.Mul:
          resultPreType = CreatePreTypeProxy("result of *");
          AddConfirmation("Mullable", resultPreType, tok,
            "type of * must be of a numeric type, bitvector type, or a set-like type (instead got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.In:
        case BinaryExpr.Opcode.NotIn:
          resultPreType = ConstrainResultToBoolFamilyOperator(tok, "'" + opString + "'");
          AddGuardedConstraint(() => {
            // For "Innable x s", if s is known, then:
            // if s == c<a> or s == c<a, b> where c is a collection type, then a :> x, else error.
            var a0 = e0.PreType.Normalize();
            var a1 = e1.PreType.Normalize();
            var coll = a1.UrAncestor(this).AsCollectionType();
            if (coll != null) {
              DebugPrint($"    DEBUG: guard applies: Innable {a0} {a1}");
              AddSubtypeConstraint(coll.Arguments[0], a0, tok, "expecting element type to be assignable to {0} (got {1})");
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
          resultPreType = CreatePreTypeProxy("result of / operation");
          AddDefaultAdvice(resultPreType, AdviceTarget.Int);
          AddConfirmation("NumericOrBitvector", resultPreType, tok, "arguments to " + opString + " must be numeric or bitvector types (got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.Mod:
          resultPreType = CreatePreTypeProxy("result of % operation");
          AddDefaultAdvice(resultPreType, AdviceTarget.Int);
          AddConfirmation("IntLikeOrBitvector", resultPreType, tok, "type of " + opString + " must be integer-numeric or bitvector types (got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.BitwiseAnd:
        case BinaryExpr.Opcode.BitwiseOr:
        case BinaryExpr.Opcode.BitwiseXor:
          resultPreType = CreatePreTypeProxy("result of " + opString + " operation");
          AddConfirmation("IsBitvector", resultPreType, tok, "type of " + opString + " must be of a bitvector type (instead got {0})");
          ConstrainOperandTypes(tok, opString, e0, e1, resultPreType);
          break;

        case BinaryExpr.Opcode.LeftShift:
        case BinaryExpr.Opcode.RightShift: {
          resultPreType = CreatePreTypeProxy("result of " + opString + " operation");
          AddConfirmation("IsBitvector", resultPreType, tok, "type of " + opString + " must be of a bitvector type (instead got {0})");
          ConstrainOperandTypes(tok, opString, e0, null, resultPreType);
          AddConfirmation("IntLikeOrBitvector", e1.PreType, tok,
            "type of right argument to " + opString + " ({0}) must be an integer-numeric or bitvector type");
          break;
        }

        default:
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected operator
      }
      // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
      // setting e.ResolvedOp until inside CheckTypeInference.
      return resultPreType;
    }

    private void ConstrainTypeExprBool(Expression e, string msgFormat) {
      Contract.Requires(e != null);
      Contract.Requires(msgFormat != null);  // may have a {0} part
      e.PreType = ConstrainResultToBoolFamily(e.tok, "<unspecified use>", msgFormat);
    }

    private void ConstrainTypeExprBool(Expression e, string proxyDescription, string msgFormat) {
      Contract.Requires(e != null);
      Contract.Requires(proxyDescription != null);
      Contract.Requires(msgFormat != null);  // may have a {0} part
      e.PreType = ConstrainResultToBoolFamily(e.tok, proxyDescription, msgFormat);
    }

    private PreType ConstrainResultToBoolFamilyOperator(IToken tok, string opString) {
      var proxyDescription = $"result of {opString} operation";
      return ConstrainResultToBoolFamily(tok, proxyDescription, "type of " + opString + " must be a boolean (got {0})");
    }

    private PreType ConstrainResultToBoolFamily(IToken tok, string proxyDescription, string errorFormat) {
      var pt = CreatePreTypeProxy(proxyDescription);
      AddDefaultAdvice(pt, AdviceTarget.Bool);
      AddConfirmation("InBoolFamily", pt, tok, errorFormat);
      return pt;
    }

    private void ConstrainToIntFamily(PreType preType, IToken tok, string errorFormat) {
      AddDefaultAdvice(preType, AdviceTarget.Int);
      AddConfirmation("InIntFamily", preType, tok, errorFormat);
    }

    private void ConstrainToCommonSupertype(IToken tok, string opString, PreType a, PreType b, PreType commonSupertype) {
      if (commonSupertype == null) {
        commonSupertype = CreatePreTypeProxy($"element type of common {opString} supertype");
      }
      var errorFormat = $"arguments to {opString} must have a common supertype (got {{0}} and {{1}})";
      AddSubtypeConstraint(commonSupertype, a, tok, errorFormat);
      AddSubtypeConstraint(commonSupertype, b, tok, errorFormat);
    }

    private void ConstrainOperandTypes(IToken tok, string opString, Expression e0, Expression e1, PreType resultPreType) {
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
    (MemberDecl/*?*/, DPreType/*?*/) FindMember(IToken tok, PreType receiverPreType, string memberName) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverPreType != null);
      Contract.Requires(memberName != null);

      PartiallySolveTypeConstraints();
      receiverPreType = receiverPreType.Normalize();
      DPreType dReceiver = null;
      if (receiverPreType is PreTypeProxy proxy) {
        // If there is a subtype constraint "proxy :> sub<X>", then (if the program is legal at all, then) "sub" must have the member "memberName".
        foreach (var sub in AllSubBounds(proxy, new HashSet<PreTypeProxy>())) {
          dReceiver = sub;
          break;
        }
        if (dReceiver == null) {
          // If there is a subtype constraint "super<X> :> proxy" where "super" has a member "memberName", then that is the correct member.
          foreach (var super in AllSuperBounds(proxy, new HashSet<PreTypeProxy>())) {
            if (super.Decl is TopLevelDeclWithMembers md && resolver.classMembers[md].ContainsKey(memberName)) {
              dReceiver = super;
              break;
            }
          }
        }
        if (dReceiver == null) {
          ReportError(tok, "type of the receiver is not fully determined at this program point");
          return (null, null);
        }
      } else {
        dReceiver = (DPreType)receiverPreType;
      }
      Contract.Assert(dReceiver != null);

      var receiverDecl = dReceiver.Decl;
      if (receiverDecl is TopLevelDeclWithMembers receiverDeclWithMembers) {
        // TODO: does this case need to do something like this?  var cd = ctype?.AsTopLevelTypeWithMembersBypassInternalSynonym;

        if (!resolver.classMembers[receiverDeclWithMembers].TryGetValue(memberName, out var member)) {
          if (memberName == "_ctor") {
            ReportError(tok, $"{receiverDecl.WhatKind} '{receiverDecl.Name}' does not have an anonymous constructor");
          } else {
            ReportError(tok, $"member '{memberName}' does not exist in {receiverDecl.WhatKind} '{receiverDecl.Name}'");
          }
          return (null, null);
        } else if (resolver.VisibleInScope(member)) {
          // TODO: We should return the original "member", not an overridden member. Alternatively, we can just return "member" so that the
          // caller can figure out the types, and then a later pass can figure out which particular "member" is intended.
          return (member, dReceiver);
        }

      } else if (receiverDecl is ValuetypeDecl valuetypeDecl) {
        if (valuetypeDecl.Members.TryGetValue(memberName, out var member)) {
          return (member, dReceiver);
        }
      }
      ReportError(tok, $"member '{memberName}' does not exist in {receiverDecl.WhatKind} '{receiverDecl.Name}'");
      return (null, null);
    }

    /// <summary>
    /// Expecting that "preType" is a type that does not involve traits, return that type, if possible.
    /// </summary>
    DPreType/*?*/ FindDefinedPreType(PreType preType) {
      Contract.Requires(preType != null);

      PartiallySolveTypeConstraints();
      preType = preType.Normalize();
      if (preType is PreTypeProxy proxy) {
        // We're looking a type with concerns for traits, so if the proxy has any sub- or super-type, then (if the
        // program is legal at all, then) that sub- or super-type must be the type we're looking for.
        foreach (var sub in AllSubBounds(proxy, new HashSet<PreTypeProxy>())) {
          return sub;
        }
        foreach (var super in AllSuperBounds(proxy, new HashSet<PreTypeProxy>())) {
          return super;
        }
        return null;
      }

      return preType as DPreType;
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
    /// <param name="complain"></param>
    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
      ResolutionContext resolutionContext, bool allowMethodCall, bool complain = true) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          resolver.ResolveType(expr.tok, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      // For 1 and 4:
      MemberDecl member = null;
      // For 2 and 5:
      Tuple<DatatypeCtor, bool> pair;

      var name = resolutionContext.InReveal ? "reveal_" + expr.Name : expr.Name;
      var v = scope.Find(name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          if (complain) {
            ReportError(expr.tok, "variable '{0}' does not take any type parameters", name);
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        }
#if NO_LONGER_NEEDED
        if (v.PreType == null) {
          v.PreType = Type2PreType(v.Type, $"type of identifier '{name}'");
        }
#endif
        r = new IdentifierExpr(expr.tok, v) {
          PreType = v.PreType
        };
      } else if (currentClass is TopLevelDeclWithMembers cl && resolver.classMembers.TryGetValue(cl, out var members) &&
                 members.TryGetValue(name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, UserDefinedType.FromTopLevelDecl(expr.tok, currentClass, currentClass.TypeArgs),
            (TopLevelDeclWithMembers)member.EnclosingClass, true);
          receiver.PreType = Type2PreType(receiver.Type);
        } else {
          if (!scope.AllowInstance) {
            if (complain) {
              ReportError(expr.tok, "'this' is not allowed in a 'static' resolutionContext"); //TODO: Rephrase this
            } else {
              expr.ResolvedExpression = null;
              return null;
            }
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = Resolver.GetThisType(expr.tok, currentClass);
          receiver.PreType = Type2PreType(receiver.Type);
        }
        r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);

      } else if (isLastNameSegment && resolver.moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 2. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }

      } else if (resolver.moduleInfo.TopLevels.TryGetValue(name, out var decl)) {
        // ----- 3. Member of the enclosing module
        if (decl is Resolver.AmbiguousTopLevelDecl ambiguousTopLevelDecl) {
          if (complain) {
            ReportError(expr.tok,
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
            if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
              // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
              // the name of the class, C. Report an error and continue.
              if (complain) {
                ReportError(expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              } else {
                expr.ResolvedExpression = null;
                return null;
              }
            }
          }
          r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
        }

      } else if (resolver.moduleInfo.StaticMembers.TryGetValue(name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (member is Resolver.AmbiguousMemberDecl ambiguousMember) {
          if (complain) {
            ReportError(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ambiguousMember.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
          receiver.PreType = Type2PreType(receiver.Type);
          r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
        }

      } else if (!isLastNameSegment && resolver.moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 5. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }

      } else {
        // ----- None of the above
        if (complain) {
          ReportError(expr.tok, "unresolved identifier: {0}", name);
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

    private Resolver_IdentifierExpr CreateResolver_IdentifierExpr(IToken tok, string name, List<Type> optTypeArguments, TopLevelDecl decl) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<Resolver_IdentifierExpr>() != null);

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
      return new Resolver_IdentifierExpr(tok, decl, typeArguments);
    }

    private bool ResolveDatatypeConstructor(NameSegment expr, List<ActualBinding>/*?*/ args, ResolutionContext resolutionContext, bool complain,
      Tuple<DatatypeCtor, bool> pair, string name, ref Expression r, ref Expression rWithArgs) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

      var datatypeDecl = pair.Item1.EnclosingDatatype;
      if (pair.Item2) {
        // there is more than one constructor with this name
        if (complain) {
          ReportError(expr.tok,
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
          ReportError(expr.tok, errorMsg);
          return false;
        } else {
          expr.ResolvedExpression = null;
          return true;
        }
      }

      var rr = new DatatypeValue(expr.tok, datatypeDecl.Name, name, args ?? new List<ActualBinding>());
      var ok = ResolveDatatypeValue(resolutionContext, rr, datatypeDecl, null, complain);
      if (!ok) {
        expr.ResolvedExpression = null;
        return true;
      }
      if (args == null) {
        r = rr;
      } else {
        r = rr; // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
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
    Expression ResolveDotSuffix(ExprDotName expr, bool isLastNameSegment, List<ActualBinding> args, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      // resolve the LHS expression
      // LHS should not be reveal lemma
      ResolutionContext nonRevealOpts = resolutionContext with { InReveal = false };
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment((NameSegment)expr.Lhs, false, null, nonRevealOpts, false);
      } else if (expr.Lhs is ExprDotName) {
        ResolveDotSuffix((ExprDotName)expr.Lhs, false, null, nonRevealOpts, false);
      } else {
        ResolveExpression(expr.Lhs, nonRevealOpts);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          resolver.ResolveType(expr.tok, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      var name = resolutionContext.InReveal ? "reveal_" + expr.SuffixName : expr.SuffixName;
      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.PreType is PreTypePlaceholderModule) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).AccessibleSignature(resolver.useCompileSignatures);
        sig = Resolver.GetSignatureExt(sig, resolver.useCompileSignatures);

        if (isLastNameSegment && sig.Ctors.TryGetValue(name, out var pair)) {
          // ----- 0. datatype constructor
          if (pair.Item2) {
            // there is more than one constructor with this name
            ReportError(expr.tok, "the name '{0}' denotes a datatype constructor in module {2}, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", name, pair.Item1.EnclosingDatatype.Name, ((ModuleDecl)ri.Decl).Name);
          } else {
            if (expr.OptTypeArguments != null) {
              ReportError(expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
            }
            var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
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
          if (decl is Resolver.AmbiguousTopLevelDecl) {
            var ad = (Resolver.AmbiguousTopLevelDecl)decl;
            ReportError(expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ad.ModuleNames());
          } else {
            // We have found a module name or a type name, neither of which is an expression. However, the ExprDotName we're
            // looking at may be followed by a further suffix that makes this into an expression. We postpone the rest of the
            // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            if (!isLastNameSegment) {
              if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
                // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
                // the name of the class, C. Report an error and continue.
                ReportError(expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              }
            }
            r = resolver.CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
          }
        } else if (sig.StaticMembers.TryGetValue(name, out var member)) {
          // ----- 2. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (member is Resolver.AmbiguousMemberDecl) {
            var ambiguousMember = (Resolver.AmbiguousMemberDecl)member;
            ReportError(expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ambiguousMember.ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        } else {
          ReportError(expr.tok, "unresolved identifier: {0}", name);
        }

      } else if (lhs != null && lhs.PreType is PreTypePlaceholderType) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 3. Look up name in type
        // expand any synonyms
        var ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs).NormalizeExpand();
        if (ty.IsDatatype) {
          // ----- LHS is a datatype
          var dt = ty.AsDatatype;
          if (dt.ConstructorsByName != null && dt.ConstructorsByName.TryGetValue(name, out var ctor)) {
            if (expr.OptTypeArguments != null) {
              ReportError(expr.tok, $"datatype constructor does not take any type parameters ('{name}')");
            }
            var rr = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
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
        if (cd != null) {
          // ----- LHS is a type with members
          if (resolver.classMembers.TryGetValue(cd, out var members) && members.TryGetValue(name, out var member)) {
            if (!resolver.VisibleInScope(member)) {
              ReportError(expr.tok, $"member '{name}' has not been imported in this scope and cannot be accessed here");
            }
            if (!member.IsStatic) {
              ReportError(expr.tok, $"accessing member '{name}' requires an instance expression"); //TODO Unify with similar error messages
              // nevertheless, continue creating an expression that approximates a correct one
            }
            var receiver = new StaticReceiverExpr(expr.tok, (UserDefinedType)ty.NormalizeExpand(), (TopLevelDeclWithMembers)member.EnclosingClass, false);
            receiver.PreType = Type2PreType(receiver.Type);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
        if (r == null) {
          ReportError(expr.tok, "member '{0}' does not exist in {2} '{1}'", name, ri.Decl.Name, ri.Decl.WhatKind);
        }

      } else if (lhs != null) {
        // ----- 4. Look up name in the type of the Lhs
        var (member, tentativeReceiverType) = FindMember(expr.tok, expr.Lhs.PreType, name);
        if (member != null) {
          if (!member.IsStatic) {
            var receiver = expr.Lhs;
            AddSubtypeConstraint(tentativeReceiverType, receiver.PreType, expr.tok, $"receiver type ({{1}}) does not have a member named '{name}'");
            r = ResolveExprDotCall(expr.tok, receiver, tentativeReceiverType, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (TopLevelDeclWithMembers)tentativeReceiverType.Decl, true);
            receiver.PreType = Type2PreType(receiver.Type);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .PreType
        expr.PreType = CreatePreTypeProxy("ExprDotName error, so using proxy instead");
      } else {
        expr.ResolvedExpression = r;
        // TODO: do we need something analogous to this for pre-types?  expr.Type = r.Type.UseInternalSynonym();
        expr.PreType = r.PreType;
      }
      return rWithArgs;
    }

    Expression ResolveExprDotCall(IToken tok, Expression receiver, DPreType receiverPreTypeBound/*?*/,
      MemberDecl member, List<ActualBinding> args, List<Type> optTypeArguments, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.PreType.Normalize() is DPreType);
      Contract.Requires(member != null);
      Contract.Requires(resolutionContext != null && resolutionContext != null);

      receiverPreTypeBound ??= (DPreType)receiver.PreType.Normalize();

      var rr = new MemberSelectExpr(tok, receiver, member.Name);
      rr.Member = member;

      // Now, fill in rr.PreType.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      rr.PreTypeApplication_AtEnclosingClass = new List<PreType>();
      rr.PreTypeApplication_JustMember = new List<PreType>();
      var rType = receiverPreTypeBound;
      var subst = PreType.PreTypeSubstMap(rType.Decl.TypeArgs, rType.Arguments);
      if (member.EnclosingClass == null) {
        // this can happen for some special members, like real.Floor
      } else {
        rr.PreTypeApplication_AtEnclosingClass.AddRange(rType.AsParentType(member.EnclosingClass, this).Arguments);
      }

      if (member is Field field) {
        if (optTypeArguments != null) {
          ReportError(tok, "a field ({0}) does not take any type arguments (got {1})", field.Name, optTypeArguments.Count);
        }
        subst = BuildPreTypeArgumentSubstitute(subst, receiverPreTypeBound);
        rr.PreType = Type2PreType(field.Type).Substitute(subst);
#if SOON
        resolver.AddCallGraphEdgeForField(resolutionContext, field, rr);
#endif
      } else if (member is Function function) {
        if (function is TwoStateFunction && !resolutionContext.IsTwoState) {
          ReportError(tok, "two-state function ('{0}') can only be called in a two-state resolutionContext", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != function.TypeArgs.Count) {
          ReportError(tok, "function '{0}' expects {1} type argument{2} (got {3})",
            member.Name, function.TypeArgs.Count, Util.Plural(function.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < function.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? Type2PreType(optTypeArguments[i]) :
            CreatePreTypeProxy($"function call to {function.Name}, type argument {i}");
          rr.PreTypeApplication_JustMember.Add(ta);
          subst.Add(function.TypeArgs[i], ta);
        }
        subst = BuildPreTypeArgumentSubstitute(subst, receiverPreTypeBound);
        var inParamTypes = function.Formals.ConvertAll(f => f.PreType.Substitute(subst));
        var resultType = Type2PreType(function.ResultType).Substitute(subst);
        rr.PreType = BuiltInArrowType(inParamTypes, resultType);
#if SOON
        AddCallGraphEdge(resolutionContext, function, rr, IsFunctionReturnValue(function, args, resolutionContext));
#endif
      } else {
        // the member is a method
        var method = (Method)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given resolutionContext
          ReportError(tok, "expression is not allowed to invoke a {0} ({1})", member.WhatKind, member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != method.TypeArgs.Count) {
          ReportError(tok, "method '{0}' expects {1} type argument{2} (got {3})",
            member.Name, method.TypeArgs.Count, Util.Plural(method.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < method.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? Type2PreType(optTypeArguments[i]) :
            CreatePreTypeProxy($"method call to {method.Name}, type argument {i}");
          rr.PreTypeApplication_JustMember.Add(ta);
          subst.Add(method.TypeArgs[i], ta);
        }
        subst = BuildPreTypeArgumentSubstitute(subst, receiverPreTypeBound);
#if SOON
        rr.ResolvedOutparameterTypes = method.Outs.ConvertAll(f => f.PreType.Substitute(subst));
#endif
        rr.PreType = new UnusedPreType($"call to {method.WhatKind} {method.Name}");  // fill in this field, in order to make "rr" resolved
      }
      return rr;
    }

    MethodCallInformation ResolveApplySuffix(ApplySuffix e, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(e != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<MethodCallInformation>() == null || allowMethodCall);

      Expression r = null;  // upon success, the expression to which the ApplySuffix resolves
      var errorCount = ErrorCount;
      if (e.Lhs is NameSegment) {
        r = ResolveNameSegment((NameSegment)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else if (e.Lhs is ExprDotName) {
        r = ResolveDotSuffix((ExprDotName)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
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
        atLabel = dominatingStatementLabels.Find(e.AtTok.val);
        if (atLabel == null) {
          ReportError(e.AtTok, "no label '{0}' in scope at this time", e.AtTok.val);
        }
      }
      if (r == null) {
        // e.Lhs denotes a function value, or at least it's used as if it were
        var dp = FindDefinedPreType(e.Lhs.PreType);
        if (dp != null && DPreType.IsArrowType(dp.Decl)) {
          // e.Lhs does denote a function value
          // In the general case, we'll resolve this as an ApplyExpr, but in the more common case of the Lhs
          // naming a function directly, we resolve this as a FunctionCallExpr.
          var mse = e.Lhs is NameSegment || e.Lhs is ExprDotName ? e.Lhs.Resolved as MemberSelectExpr : null;
          var callee = mse?.Member as Function;
          if (atLabel != null && !(callee is TwoStateFunction)) {
            ReportError(e.AtTok, "an @-label can only be applied to a two-state function");
            atLabel = null;
          }
          if (callee != null) {
            // resolve as a FunctionCallExpr instead of as an ApplyExpr(MemberSelectExpr)
            var rr = new FunctionCallExpr(e.Lhs.tok, callee.Name, mse.Obj, e.tok, e.CloseParen, e.Bindings, atLabel) {
              Function = callee,
              PreTypeApplication_AtEnclosingClass = mse.PreTypeApplication_AtEnclosingClass,
              PreTypeApplication_JustFunction = mse.PreTypeApplication_JustMember
            };
            var typeMap = mse.PreTypeArgumentSubstitutionsAtMemberDeclaration();
            var preTypeMap = BuildPreTypeArgumentSubstitute(
                typeMap.Keys.ToDictionary(tp => tp, tp => typeMap[tp]));
            ResolveActualParameters(rr.Bindings, callee.Formals, e.tok, callee, resolutionContext, preTypeMap, callee.IsStatic ? null : mse.Obj);
            rr.PreType = Type2PreType(callee.ResultType).Substitute(preTypeMap);
            if (errorCount == ErrorCount) {
              Contract.Assert(!(mse.Obj is StaticReceiverExpr) || callee.IsStatic);  // this should have been checked already
              Contract.Assert(callee.Formals.Count == rr.Args.Count);  // this should have been checked already
            }
            // further bookkeeping
            if (callee is ExtremePredicate) {
              ((ExtremePredicate)callee).Uses.Add(rr);
            }
            r = rr;
            ResolveExpression(r, resolutionContext);
          } else {
            // resolve as an ApplyExpr
            var formals = new List<Formal>();
            for (var i = 0; i < dp.Arguments.Count - 1; i++) {
              var argType = dp.Arguments[i];
              var formal = new ImplicitFormal(e.tok, "_#p" + i, new InferredTypeProxy(), true, false);
              formal.PreType = argType;
              formals.Add(formal);
            }
            ResolveActualParameters(e.Bindings, formals, e.tok, dp, resolutionContext, new Dictionary<TypeParameter, PreType>(), null);
            r = new ApplyExpr(e.Lhs.tok, e.Lhs, e.Args, e.CloseParen);
            ResolveExpression(r, resolutionContext);
            r.PreType = dp.Arguments.Last();
          }
        } else {
          // e.Lhs is used as if it were a function value, but it isn't
          var lhs = e.Lhs.Resolved;
          if (lhs != null && lhs.PreType is PreTypePlaceholderModule) {
            ReportError(e.tok, "name of module ({0}) is used as a function", ((Resolver_IdentifierExpr)lhs).Decl.Name);
          } else if (lhs != null && lhs.PreType is PreTypePlaceholderType) {
            var ri = (Resolver_IdentifierExpr)lhs;
            ReportError(e.tok, "name of {0} ({1}) is used as a function", ri.Decl.WhatKind, ri.Decl.Name);
          } else {
            if (lhs is MemberSelectExpr mse && mse.Member is Method) {
              if (atLabel != null) {
                Contract.Assert(mse != null); // assured by the parser
                if (mse.Member is TwoStateLemma) {
                  mse.AtLabel = atLabel;
                } else {
                  ReportError(e.AtTok, "an @-label can only be applied to a two-state lemma");
                }
              }
              if (allowMethodCall) {
                return new MethodCallInformation(e.RangeToken, mse, e.Bindings.ArgumentBindings);
              } else {
                ReportError(e.tok, "{0} call is not allowed to be used in an expression resolutionContext ({1})", mse.Member.WhatKind, mse.Member.Name);
              }
            } else if (lhs != null) {  // if e.Lhs.Resolved is null, then e.Lhs was not successfully resolved and an error has already been reported
              ReportError(e.tok, "non-function expression (of type {0}) is called with parameters", e.Lhs.Type);
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
    /// </summary>
    Expression ResolveDatatypeUpdate(IToken tok, DPreType rootPreType, Expression root, DatatypeDecl dt,
      List<Tuple<IToken, string, Expression>> memberUpdates,
      ResolutionContext resolutionContext, out List<DatatypeCtor> legalSourceConstructors) {
      Contract.Requires(tok != null);
      Contract.Requires(root != null);
      Contract.Requires(rootPreType != null);
      Contract.Requires(dt != null);
      Contract.Requires(memberUpdates != null);
      Contract.Requires(resolutionContext != null);

      legalSourceConstructors = null;
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
          if (!resolver.classMembers[dt].TryGetValue(updateName, out var member)) {
            ReportError(updateToken, "member '{0}' does not exist in datatype '{1}'", updateName, dt.Name);
          } else if (!(member is DatatypeDestructor)) {
            ReportError(updateToken, "member '{0}' is not a destructor in datatype '{1}'", updateName, dt.Name);
          } else {
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
                var xVar = new BoundVar(new AutoGeneratedToken(tok), xName, new InferredTypeProxy());
                var x = new IdentifierExpr(new AutoGeneratedToken(tok), xVar);
                rhsBindings.Add(updateName, new Tuple<BoundVar, IdentifierExpr, Expression>(xVar, x, updateValue));
              }
            }
          }
        }
      }
      if (candidateResultCtors.Count == 0) {
        return null;
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
        return null;
      }

      // The legal source constructors are the candidate result constructors. (Yep, two names for the same thing.)
      legalSourceConstructors = candidateResultCtors;
      Contract.Assert(1 <= legalSourceConstructors.Count);

      return DesugarDatatypeUpdate(tok, root, dt, resolutionContext, rootPreType, candidateResultCtors, rhsBindings);
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
    private Expression DesugarDatatypeUpdate(IToken tok, Expression root, DatatypeDecl dt, ResolutionContext resolutionContext, DPreType rootPreType,
      List<DatatypeCtor> candidateResultCtors, Dictionary<string, Tuple<BoundVar, IdentifierExpr, Expression>> rhsBindings) {
      Contract.Requires(1 <= candidateResultCtors.Count);

      // Create a unique name for d', the variable we introduce in the let expression
      var dName = resolver.FreshTempVarName("dt_update_tmp#", resolutionContext.CodeContext);
      var dVar = new BoundVar(new AutoGeneratedToken(tok), dName, new InferredTypeProxy());
      dVar.PreType = rootPreType;
      var d = new IdentifierExpr(new AutoGeneratedToken(tok), dVar);
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
            ctorArg = new ExprDotName(tok, d, f.Name, null);
          }
          var bindingName = new Token(tok.line, tok.col) {
            Filename = tok.filename,
            val = f.Name
          };
          actualBindings.Add(new ActualBinding(bindingName, ctorArg));
        }
        var ctorCall = new DatatypeValue(tok, crc.EnclosingDatatype.Name, crc.Name, actualBindings);
        if (body == null) {
          body = ctorCall;
        } else {
          // body := if d.crc? then ctor_call else body
          var guard = new ExprDotName(tok, d, crc.QueryField.Name, null);
          body = new ITEExpr(tok, false, guard, ctorCall, body);
        }
      }
      Contract.Assert(body != null); // because there was at least one element in candidateResultCtors

      // Wrap the let bindings around body
      var rewrite = body;
      foreach (var entry in rhsBindings) {
        if (entry.Value.Item1 != null) {
          var lhs = new CasePattern<BoundVar>(tok, entry.Value.Item1);
          rewrite = new LetExpr(tok, new List<CasePattern<BoundVar>>() { lhs }, new List<Expression>() { entry.Value.Item3 }, rewrite, true);
        }
      }
      var dVarPat = new CasePattern<BoundVar>(tok, dVar);
      rewrite = new LetExpr(tok, new List<CasePattern<BoundVar>>() { dVarPat }, new List<Expression>() { root }, rewrite, true);
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
#if SOON
        AddTypeDependencyEdges(resolutionContext, v.Type);
#endif
        // Note, the following type constraint checks that the RHS type can be assigned to the new variable on the left. In particular, it
        // does not check that the entire RHS can be assigned to something of the type of the pattern on the left.  For example, consider
        // a type declared as "datatype Atom<T> = MakeAtom(T)", where T is a non-variant type argument.  Suppose the RHS has type Atom<nat>
        // and that the LHS is the pattern MakeAtom(x: int).  This is okay, despite the fact that Atom<nat> is not assignable to Atom<int>.
        // The reason is that the purpose of the pattern on the left is really just to provide a skeleton to introduce bound variables in.
#if SOON
        EagerAddAssignableConstraint(v.Tok, v.Type, sourcePreType, "type of corresponding source/RHS ({1}) does not match type of bound variable ({0})");
#else
        AddSubtypeConstraint(v.PreType, sourcePreType, v.Tok,
          "type of corresponding source/RHS ({1}) does not match type of bound variable ({0})");
#endif
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
          AddSubtypeConstraint(lhsPreType, sourcePreType, pat.tok, $"type of RHS ({{0}}) does not match type of bound variable '{pat.Id}' ({{1}})");
        }
      }
      if (dtd == null) {
        Contract.Assert(ctor == null);
        ReportError(pat.tok, "to use a pattern, the type of the source/RHS expression must be a datatype (instead found {0})", sourcePreType);
      } else if (ctor == null) {
        ReportError(pat.tok, "constructor {0} does not exist in datatype {1}", pat.Id, dtd.Name);
      } else {
        if (pat.Arguments == null) {
          if (ctor.Formals.Count == 0) {
            // The Id matches a constructor of the correct type and 0 arguments,
            // so make it a nullary constructor, not a variable
            pat.MakeAConstructor();
          }
        } else {
          if (ctor.Formals.Count != pat.Arguments.Count) {
            ReportError(pat.tok, "pattern for constructor {0} has wrong number of formals (found {1}, expected {2})", pat.Id, pat.Arguments.Count, ctor.Formals.Count);
          }
        }
        // build the type-parameter substitution map for this use of the datatype
        Contract.Assert(dtd.TypeArgs.Count == sourceTypeArguments.Count);  // follows from the type previously having been successfully resolved
        var subst = PreType.PreTypeSubstMap(dtd.TypeArgs, sourceTypeArguments);
        // recursively call ResolveCasePattern on each of the arguments
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
        if (j == ctor.Formals.Count) {
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
          ReportError(dtv.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
        }
      } else {
        Contract.Assert(ctor != null); // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
      }
      if (complain && ctor != null) {
        var subst = PreType.PreTypeSubstMap(datatypeDecl.TypeArgs, gt);
        ResolveActualParameters(dtv.Bindings, ctor.Formals, dtv.tok, ctor, resolutionContext, subst, null);
      } else {
        // still resolve the expressions
        foreach (var binding in dtv.Bindings.ArgumentBindings) {
          ResolveExpression(binding.Actual, resolutionContext);
        }
        dtv.Bindings.AcceptArgumentExpressionsAsExactParameterList();
      }

      if (CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is ICallable caller && caller.EnclosingModule == datatypeDecl.EnclosingModuleDefinition) {
        caller.EnclosingModule.CallGraph.AddEdge(caller, datatypeDecl);
      }
      return ok && ctor.Formals.Count == dtv.Arguments.Count;
    }

    PreType ResolveSingleSelectionExpr(IToken tok, PreType collectionPreType, Expression index) {
      var resultPreType = CreatePreTypeProxy("seq selection");
      AddGuardedConstraint(() => {
        var sourcePreType = collectionPreType.Normalize() as DPreType;
        if (sourcePreType != null) {
          var familyDeclName = AncestorName(sourcePreType);
          switch (familyDeclName) {
            case "array":
            case "seq":
              ConstrainToIntFamily(index.PreType, index.tok, "index expression must have an integer type (got {0})");
              AddSubtypeConstraint(resultPreType, sourcePreType.Arguments[0], tok, "type does not agree with element type {1} (got {0})");
              break;
            case "multiset":
              AddSubtypeConstraint(sourcePreType.Arguments[0], index.PreType, index.tok, "type does not agree with element type {0} (got {1})");
              ConstrainToIntFamily(resultPreType, tok, "multiset multiplicity must have an integer type (got {0})");
              break;
            case "map":
            case "imap":
              AddSubtypeConstraint(sourcePreType.Arguments[0], index.PreType, index.tok, "type does not agree with domain type {0} (got {1})");
              AddSubtypeConstraint(resultPreType, sourcePreType.Arguments[1], tok, "type does not agree with value type of {1} (got {0})");
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

    PreType ResolveRangeSelectionExpr(IToken tok, PreType collectionPreType, Expression e0, Expression e1) {
      var resultElementPreType = CreatePreTypeProxy("multi-index selection");
      var resultPreType = new DPreType(BuiltInTypeDecl("seq"), new List<PreType>() { resultElementPreType });
      if (e0 != null) {
        ConstrainToIntFamily(e0.PreType, e0.tok, "multi-element selection position expression must have an integer type (got {0})");
      }
      if (e1 != null) {
        ConstrainToIntFamily(e1.PreType, e1.tok, "multi-element selection position expression must have an integer type (got {0})");
      }
      AddGuardedConstraint(() => {
        var sourcePreType = collectionPreType.Normalize() as DPreType;
        if (sourcePreType != null) {
          var familyDeclName = AncestorName(sourcePreType);
          switch (familyDeclName) {
            case "seq":
            case "array":
              AddSubtypeConstraint(resultElementPreType, sourcePreType.Arguments[0], tok, "type does not agree with element type {1} (got {0})");
              break;
            default:
              ReportError(tok, "multi-selection of elements requires a sequence or array (got {0})", collectionPreType);
              break;
          }
          return true;
        }
        return false;
      });
      return resultPreType;
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
      return resolver.LetVarIn(expr.tok, burrito, burritoType, expr.Rhs,
        // "if burrito.IsFailure()"
        new ITEExpr(expr.tok, false, resolver.VarDotFunction(expr.tok, burrito, "IsFailure"),
          // "then burrito.PropagateFailure()"
          resolver.VarDotFunction(expr.tok, burrito, "PropagateFailure"),
          // "else"
          expr.Lhs == null
            // "Body"
            ? expr.Body
            // "var x: T := burrito.Extract(); Body"
            : resolver.LetPatIn(expr.tok, expr.Lhs, resolver.VarDotFunction(expr.tok, burrito, "Extract"), expr.Body)));
    }

    private void EnsureSupportsErrorHandling(IToken tok, DPreType burritoPreType, bool expectExtract, string keyword = null) {
      Contract.Requires(tok != null);
      Contract.Requires(burritoPreType != null);

      var (memberIsFailure, _) = FindMember(tok, burritoPreType, "IsFailure");
      var (memberPropagate, _) = FindMember(tok, burritoPreType, "PropagateFailure");
      var (memberExtract, _) = FindMember(tok, burritoPreType, "Extract");

      if (keyword != null) {
        if (memberIsFailure == null || (memberExtract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract ? "members IsFailure() and Extract()" : "member IsFailure(), but not Extract()";
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

  }
}
