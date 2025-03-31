//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;


namespace Microsoft.Dafny {
  public class TypeCharacteristicChecker {

    /// <summary>
    /// Infer required equality support from looking at signatures of declarations.
    /// Then, check that all type characteristics are used and passed in properly.
    ///
    /// Note that this method can only be called after determining which expressions are ghosts.
    /// </summary>
    public static void InferAndCheck(List<TopLevelDecl> declarations, bool isAnExport, ErrorReporter reporter) {
      InferEqualitySupport(declarations, reporter);
      Check(declarations, isAnExport, reporter);
    }

    /// <summary>
    /// Inferred required equality support for datatypes and type synonyms, and for Function and Method signatures.
    /// </summary>
    private static void InferEqualitySupport(List<TopLevelDecl> declarations, ErrorReporter reporter) {
      // First, do datatypes and type synonyms until a fixpoint is reached.
      bool inferredSomething;
      do {
        inferredSomething = false;
        foreach (var d in declarations) {
          if (Attributes.Contains(d.Attributes, "_provided")) {
            // Don't infer required-equality-support for the type parameters, since there are
            // scopes that see the name of the declaration but not its body.
          } else if (d is DatatypeDecl dt) {
            foreach (var tp in dt.TypeArgs) {
              if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                inferredSomething = inferredSomething || dt.Ctors.Any(ctor =>
                  ctor.Formals.Any(arg =>
                    InferAndSetEqualitySupport(tp, arg.Type, reporter)
                  )
                ) || dt.Traits.Any(parentType =>
                  InferAndSetEqualitySupport(tp, parentType, reporter)
                );
              }
            }
          } else if (d is TypeSynonymDecl syn) {
            foreach (var tp in syn.TypeArgs) {
              if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                // here's our chance to infer the need for equality support
                if (InferAndSetEqualitySupport(tp, syn.Rhs, reporter)) {
                  inferredSomething = true;
                }
              }
            }
          } else if (d is NewtypeDecl newtypeDecl) {
            foreach (var tp in newtypeDecl.TypeArgs) {
              if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                // here's our chance to infer the need for equality support
                if (InferAndSetEqualitySupport(tp, newtypeDecl.BaseType, reporter)) {
                  inferredSomething = true;
                }
              }
            }
          }
        }
      } while (inferredSomething);

      // Now do it for Function and Method signatures.
      foreach (var d in declarations) {
        if (d is IteratorDecl iter) {
          var done = false;
          var nonnullIter = iter.NonNullTypeDecl;
          Contract.Assert(nonnullIter.TypeArgs.Count == iter.TypeArgs.Count);
          for (var i = 0; i < iter.TypeArgs.Count; i++) {
            var tp = iter.TypeArgs[i];
            var correspondingNonnullIterTypeParameter = nonnullIter.TypeArgs[i];
            if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
              // here's our chance to infer the need for equality support
              foreach (var p in iter.Ins) {
                if (InferAndSetEqualitySupport(tp, p.Type, reporter)) {
                  correspondingNonnullIterTypeParameter.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                  done = true;
                  break;
                }
              }

              foreach (var p in iter.Outs) {
                if (done) {
                  break;
                }
                if (InferAndSetEqualitySupport(tp, p.Type, reporter)) {
                  correspondingNonnullIterTypeParameter.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
                  break;
                }
              }
            }
          }
        } else if (d is ClassLikeDecl or DefaultClassDecl) {
          var cl = (TopLevelDeclWithMembers)d;
          foreach (var member in cl.Members.Where(member => !member.IsGhost)) {
            List<TypeParameter> memberTypeArguments = null;
            if (member is Function function) {
              memberTypeArguments = function.TypeArgs;
              foreach (var tp in function.TypeArgs) {
                if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                  // here's our chance to infer the need for equality support
                  if (InferAndSetEqualitySupport(tp, function.ResultType, reporter)) {
                    // the call to InferAndSetEqualitySupport made the necessary updates
                  } else {
                    foreach (var p in function.Ins) {
                      if (InferAndSetEqualitySupport(tp, p.Type, reporter)) {
                        break;
                      }
                    }
                  }
                }
              }
            } else if (member is MethodOrConstructor method) {
              memberTypeArguments = method.TypeArgs;
              bool done = false;
              foreach (var tp in method.TypeArgs) {
                if (tp.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified) {
                  // here's our chance to infer the need for equality support
                  foreach (var p in method.Ins) {
                    if (InferAndSetEqualitySupport(tp, p.Type, reporter)) {
                      done = true;
                      break;
                    }
                  }

                  foreach (var p in method.Outs) {
                    if (done) {
                      break;
                    }
                    if (InferAndSetEqualitySupport(tp, p.Type, reporter)) {
                      break;
                    }
                  }
                }
              }
            }

            // Now that type characteristics have been inferred for any method/function type parameters, generate a tool tip
            // if the type parameters were added as part of type-parameter completion.
            if (memberTypeArguments != null && memberTypeArguments.Count != 0 && memberTypeArguments[0].IsAutoCompleted) {
              var toolTip = $"<{memberTypeArguments.Comma(Printer.TypeParameterToString)}>";
              reporter.Info(MessageSource.Resolver, member.Origin, toolTip);
            }

          }
        }
      }
    }

    private static bool InferAndSetEqualitySupport(TypeParameter tp, Type type, ErrorReporter reporter) {
      var requiresEqualitySupport = InferRequiredEqualitySupport(tp, type);
      if (requiresEqualitySupport) {
        tp.Characteristics.EqualitySupport = TypeParameter.EqualitySupportValue.InferredRequired;
        // Note, auto-completed type parameters already get a tool tip for the enclosing method/function
        if (reporter is not ErrorReporterWrapper && !tp.IsAutoCompleted) {
          reporter.Info(MessageSource.Resolver, tp.Origin, "(==)");
        }
      }
      return requiresEqualitySupport;
    }

    private static bool InferRequiredEqualitySupport(TypeParameter tp, Type type) {
      Contract.Requires(tp != null);
      Contract.Requires(type != null);

      type = type.Normalize();  // we only do a .Normalize() here, because we want to keep stop at any type synonym or subset type
      if (type is BasicType) {
      } else if (type is SetType setType) {
        return setType.Arg.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, setType.Arg);
      } else if (type is MultiSetType multiSetType) {
        return multiSetType.Arg.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, multiSetType.Arg);
      } else if (type is MapType mapType) {
        return mapType.Domain.AsTypeParameter == tp || InferRequiredEqualitySupport(tp, mapType.Domain) || InferRequiredEqualitySupport(tp, mapType.Range);
      } else if (type is SeqType seqType) {
        return InferRequiredEqualitySupport(tp, seqType.Arg);
      } else if (type is UserDefinedType udt) {
        var formalTypeArgs = udt.ResolvedClass.TypeArgs;
        Contract.Assert(formalTypeArgs != null);
        Contract.Assert(formalTypeArgs.Count == udt.TypeArgs.Count);
        var i = 0;
        foreach (var argType in udt.TypeArgs) {
          var formalTypeArg = formalTypeArgs[i];
          if ((formalTypeArg.SupportsEquality && argType.AsTypeParameter == tp) || InferRequiredEqualitySupport(tp, argType)) {
            return true;
          }
          i++;
        }
        if (udt.ResolvedClass is TypeSynonymDecl syn) {
          if (syn.IsRevealedInScope(Type.GetScope())) {
            return InferRequiredEqualitySupport(tp, syn.RhsWithArgument(udt.TypeArgs));
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return false;
    }

    private static void Check(List<TopLevelDecl> declarations, bool isAnExport, ErrorReporter reporter) {
      var visitor = new CheckTypeCharacteristicsVisitor(reporter);

      foreach (var d in declarations) {
        CheckAttributes(d.Attributes, visitor);

        if (d is IteratorDecl iter) {
          CheckFormals(iter.Ins, false, visitor);
          CheckFormals(iter.Outs, false, visitor);
          CheckSpecification(iter.Requires, iter.Modifies, iter.Ensures, iter.Decreases, visitor);
          CheckSpecification(iter.YieldRequires, iter.Reads, iter.YieldEnsures, null, visitor);
          if (iter.Body != null) {
            visitor.Visit(iter.Body, false);
          }
        } else if (d is ClassLikeDecl cl) {
          foreach (var parentTrait in cl.Traits) {
            visitor.VisitType(cl.Origin, parentTrait, false);
          }
        } else if (d is DatatypeDecl dt) {
          foreach (var ctor in dt.Ctors) {
            CheckAttributes(ctor.Attributes, visitor);
            CheckFormals(ctor.Formals, ctor.IsGhost, visitor);
          }
        } else if (d is TypeSynonymDecl syn) {
          visitor.VisitType(syn.Origin, syn.Rhs, false);
          if (!isAnExport) {
            if (syn.SupportsEquality && !syn.Rhs.SupportsEquality) {
              reporter.Error(MessageSource.Resolver, syn.Origin, "type '{0}' declared as supporting equality, but the RHS type ({1}) might not{2}",
                syn.Name, syn.Rhs, CheckTypeCharacteristicsVisitor.TypeEqualityErrorMessageHint(syn.Rhs));
            }
            if (syn.Characteristics.IsNonempty && !syn.Rhs.IsNonempty) {
              reporter.Error(MessageSource.Resolver, syn.Origin, "type '{0}' declared as being nonempty, but the RHS type ({1}) may be empty",
                syn.Name, syn.Rhs);
            } else if (syn.Characteristics.HasCompiledValue && !syn.Rhs.HasCompilableValue) {
              reporter.Error(MessageSource.Resolver, syn.Origin,
                "type '{0}' declared as auto-initialization type, but the RHS type ({1}) does not support auto-initialization", syn.Name,
                syn.Rhs);
            }
            if (syn.Characteristics.ContainsNoReferenceTypes && syn.Rhs.MayInvolveReferences) {
              reporter.Error(MessageSource.Resolver, syn.Origin,
                "type '{0}' declared as containing no reference types, but the RHS type ({1}) may contain reference types", syn.Name,
                syn.Rhs);
            }
          }
        } else if (d is NewtypeDecl { BaseType: { } baseType }) {
          visitor.VisitType(d.Origin, baseType, false);
        }

        if (d is RedirectingTypeDecl rtd) {
          if (rtd.Constraint != null) {
            // TODO: In some places, constraints are checked at run time. Those places need to be checked with isGhostContext:=false. Ugh! Better
            // would be if the language design was such that the declaration said directly whether or not the constraint is intended to be ghost
            // or compiled.
            visitor.Visit(rtd.Constraint, true);
          }
          if (rtd.Witness != null) {
            visitor.Visit(rtd.Witness, rtd.WitnessKind == SubsetTypeDecl.WKind.Ghost);
          }
        }

        if (d is TopLevelDeclWithMembers topLevelDeclWithMembers) {
          foreach (var member in topLevelDeclWithMembers.Members) {
            CheckAttributes(member.Attributes, visitor);
            if (member is Field field) {
              visitor.VisitType(field.Origin, field.Type, field.IsGhost);
              if (field is ConstantField { Rhs: { } } cf) {
                visitor.Visit(cf.Rhs, cf.IsGhost);
              }
            } else if (member is Function function) {
              CheckFormals(function.Ins, function.IsGhost, visitor);
              visitor.VisitType(function.Result?.Origin ?? function.Origin, function.ResultType, function.IsGhost);
              CheckSpecification(function.Req, function.Reads, function.Ens, function.Decreases, visitor);
              if (function.Body != null) {
                visitor.Visit(function.Body, function.IsGhost);
              }
            } else if (member is MethodOrConstructor method) {
              CheckFormals(method.Ins, method.IsGhost, visitor);
              CheckFormals(method.Outs, method.IsGhost, visitor);
              CheckSpecification(method.Req, method.Mod, method.Ens, method.Decreases, visitor);
              if (method.Body != null) {
                visitor.Visit(method.Body, method.IsGhost);
              }
            }
          }
        }
      }
    }

    private static void CheckAttributes(Attributes attributes, CheckTypeCharacteristicsVisitor visitor) {
      for (var attr = attributes; attr != null; attr = attr.Prev) {
        attr.Args.ForEach(e => visitor.Visit(e, true));
      }
    }

    private static void CheckFormals(List<Formal> formals, bool isGhostContext, CheckTypeCharacteristicsVisitor visitor) {
      foreach (var p in formals) {
        visitor.VisitType(p.Origin, p.Type, isGhostContext || p.IsGhost);
        if (p.DefaultValue != null) {
          visitor.Visit(p.DefaultValue, isGhostContext || p.IsGhost);
        }
      }
    }

    private static void CheckSpecification(List<AttributedExpression> requires, Specification<FrameExpression> frame,
      List<AttributedExpression> ensures, [CanBeNull] Specification<Expression> decreases,
      CheckTypeCharacteristicsVisitor visitor) {

      foreach (var aexpr in requires) {
        CheckAttributes(aexpr.Attributes, visitor);
        visitor.Visit(aexpr.E, true);
      }

      CheckAttributes(frame.Attributes, visitor);
      foreach (var expr in frame.Expressions) {
        visitor.Visit(expr, true);
      }

      foreach (var aexpr in ensures) {
        CheckAttributes(aexpr.Attributes, visitor);
        visitor.Visit(aexpr.E, true);
      }

      if (decreases != null) {
        CheckAttributes(decreases.Attributes, visitor);
        foreach (var expr in decreases.Expressions) {
          visitor.Visit(expr, true);
        }
      }
    }

  }
}
