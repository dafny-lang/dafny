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
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public interface IASTVisitorContext {
    ModuleDefinition EnclosingModule { get; } // to be called only after signature-resolution is complete
  }

  public abstract class ASTVisitor<VisitorContext> where VisitorContext : IASTVisitorContext {
    public ASTVisitor() {
    }

    public abstract VisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition);

    /// <summary>
    /// For every TopLevelDecl in "declarations" and every MemberDecl in such a TopLevelDecl, visit every
    /// statement and expression using "visitor".
    /// </summary>
    public void VisitDeclarations(List<TopLevelDecl> declarations) {
      declarations.ForEach(VisitOneDeclaration);
    }

    protected virtual void VisitOneDeclaration(TopLevelDecl decl) {
      VisitAttributes(decl, decl.EnclosingModuleDefinition);

      if (decl is RedirectingTypeDecl dd) {
        var context = GetContext(dd, false);
        var baseType = (decl as NewtypeDecl)?.BaseType ?? ((TypeSynonymDeclBase)decl).Rhs;
        VisitUserProvidedType(baseType, context);
        if (dd.Constraint != null) {
          VisitExpression(dd.Constraint, context);
        }
        if (dd.Witness != null) {
          VisitExpression(dd.Witness, context);
        }

      } else if (decl is IteratorDecl iteratorDecl) {
        VisitIterator(iteratorDecl);

      } else if (decl is DatatypeDecl datatypeDecl) {
        foreach (var ctor in datatypeDecl.Ctors) {
          VisitAttributes(ctor, decl.EnclosingModuleDefinition);
        }
        foreach (var ctor in datatypeDecl.Ctors) {
          var context = GetContext(datatypeDecl, false);
          VisitDefaultParameterValues(ctor.Formals, context);
        }
      }

      if (decl is TopLevelDeclWithMembers cl) {
        cl.Members.ForEach(VisitMember);
      }
    }

    private void VisitIterator(IteratorDecl iteratorDecl) {
      var context = GetContext(iteratorDecl, false);

      VisitAttributes(iteratorDecl, iteratorDecl.EnclosingModuleDefinition);

      VisitDefaultParameterValues(iteratorDecl.Ins, context);

      iteratorDecl.Requires.ForEach(aexpr => VisitAttributedExpression(aexpr, context));

      VisitAttributes(iteratorDecl.Modifies, iteratorDecl.EnclosingModuleDefinition);
      iteratorDecl.Modifies.Expressions.ForEach(frameExpr => VisitTopLevelFrameExpression(frameExpr, context));

      iteratorDecl.YieldRequires.ForEach(aexpr => VisitAttributedExpression(aexpr, context));

      iteratorDecl.Reads.Expressions.ForEach(frameExpr => VisitTopLevelFrameExpression(frameExpr, context));

      iteratorDecl.YieldEnsures.ForEach(aexpr => VisitExpression(aexpr.E, context));

      iteratorDecl.Ensures.ForEach(aexpr => VisitExpression(aexpr.E, context));

      VisitAttributes(iteratorDecl.Decreases, iteratorDecl.EnclosingModuleDefinition);
      iteratorDecl.Decreases.Expressions.ForEach(expr => VisitExpression(expr, context));

      if (iteratorDecl.Body != null) {
        VisitStatement(iteratorDecl.Body, context);
      }
    }

    public void VisitMember(MemberDecl member) {
      if (member is Field field) {
        VisitField(field);

      } else if (member is Function function) {
        VisitFunction(function);

        var prefixPredicate = (function as ExtremePredicate)?.PrefixPredicate;
        if (prefixPredicate != null) {
          VisitFunction(prefixPredicate);
        }

        if (function.ByMethodDecl != null) {
          VisitMethod(function.ByMethodDecl);
        }

      } else if (member is Method method) {
        VisitMethod(method);

        var prefixLemma = (method as ExtremeLemma)?.PrefixLemma;
        if (prefixLemma != null) {
          VisitMethod(prefixLemma);
        }

      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected member type
      }
    }

    public virtual void VisitField(Field field) {
      var enclosingModule = field.EnclosingClass.EnclosingModuleDefinition;
      VisitAttributes(field, enclosingModule);

      var context = GetContext(field as IASTVisitorContext ?? new NoContext(enclosingModule), false);
      VisitUserProvidedType(field.Type, context);

      if (field is ConstantField { Rhs: { } rhs }) {
        VisitExpression(rhs, context);
      }
    }

    public virtual void VisitFunction(Function function) {
      var context = GetContext(function, false);

      VisitAttributes(function, function.EnclosingClass.EnclosingModuleDefinition);

      foreach (var formal in function.Ins) {
        VisitUserProvidedType(formal.Type, context);
      }
      VisitUserProvidedType(function.ResultType, context);

      VisitDefaultParameterValues(function.Ins, context);

      function.Req.ForEach(aexpr => VisitAttributedExpression(aexpr, context));

      VisitAttributes(function.Reads, function.EnclosingClass.EnclosingModuleDefinition);
      function.Reads.Expressions.ForEach(frameExpression => VisitTopLevelFrameExpression(frameExpression, context));

      function.Ens.ForEach(aexpr => VisitAttributedExpression(aexpr, GetContext(function, true)));

      VisitAttributes(function.Decreases, function.EnclosingClass.EnclosingModuleDefinition);
      function.Decreases.Expressions.ForEach(expr => VisitExpression(expr, context));

      if (function.Body != null) {
        VisitExpression(function.Body, context);
      }
    }

    public virtual void VisitMethod(Method method) {
      var context = GetContext(method, false);

      VisitAttributes(method, method.EnclosingClass.EnclosingModuleDefinition);

      foreach (var p in method.Ins) {
        VisitUserProvidedType(p.Type, context);
      }
      foreach (var p in method.Outs) {
        VisitUserProvidedType(p.Type, context);
      }

      VisitDefaultParameterValues(method.Ins, context);

      method.Req.ForEach(aexpr => VisitAttributedExpression(aexpr, context));

      method.Reads.Expressions.ForEach(frameExpression => VisitTopLevelFrameExpression(frameExpression, context));

      VisitAttributes(method.Mod, method.EnclosingClass.EnclosingModuleDefinition);
      method.Mod.Expressions.ForEach(frameExpression => VisitTopLevelFrameExpression(frameExpression, context));

      VisitAttributes(method.Decreases, method.EnclosingClass.EnclosingModuleDefinition);
      method.Decreases.Expressions.ForEach(expr => VisitExpression(expr, context));

      method.Ens.ForEach(aexpr => VisitAttributedExpression(aexpr, context));

      if (method.Body != null) {
        VisitStatement(method.Body, context);
      }
    }

    private void VisitDefaultParameterValues(List<Formal> formals, VisitorContext context) {
      formals
        .Where(formal => formal.DefaultValue != null)
        .ForEach(formal => VisitExpression(formal.DefaultValue, context));
    }

    private void VisitAttributedExpression(AttributedExpression attributedExpression, VisitorContext context) {
      VisitAttributes(attributedExpression, context.EnclosingModule);
      VisitExpression(attributedExpression.E, context);
    }

    private void VisitAttributes(IAttributeBearingDeclaration parent, ModuleDefinition enclosingModule) {
      foreach (var attribute in parent.Attributes.AsEnumerable()) {
        foreach (var arg in attribute.Args ?? Enumerable.Empty<Expression>()) {
          VisitExpression(arg, GetContext(new NoContext(enclosingModule), false));
        }
      }
    }

    protected virtual void VisitUserProvidedType(Type type, VisitorContext context) {
    }

    protected virtual void VisitExpression(Expression expr, VisitorContext context) {
      if (VisitOneExpression(expr, context)) {
        // Visit user-provided types
        if (expr is SeqConstructionExpr seqConstructionExpr) {
          var userProvidedElementType = seqConstructionExpr.ExplicitElementType;
          if (userProvidedElementType != null) {
            VisitUserProvidedType(userProvidedElementType, context);
          }

        } else if (expr is TypeUnaryExpr typeUnaryExpr) {
          VisitUserProvidedType(typeUnaryExpr.ToType, context);

        } else if (expr is LetExpr letExpr) {
          foreach (var lhs in letExpr.LHSs) {
            foreach (var v in lhs.Vars) {
              VisitUserProvidedType(v.SyntacticType, context);
            }
          }

        } else if (expr is QuantifierExpr quantifierExpr) {
          foreach (BoundVar v in quantifierExpr.BoundVars) {
            VisitUserProvidedType(v.Type, context);
          }

        } else if (expr is SetComprehension setComprehension) {
          foreach (BoundVar v in setComprehension.BoundVars) {
            VisitUserProvidedType(v.Type, context);
          }

        } else if (expr is MapComprehension mapComprehension) {
          foreach (BoundVar v in mapComprehension.BoundVars) {
            VisitUserProvidedType(v.Type, context);
          }

        } else if (expr is LambdaExpr lambdaExpr) {
          foreach (BoundVar v in lambdaExpr.BoundVars) {
            VisitUserProvidedType(v.Type, context);
          }

        } else if (expr is MatchExpr matchExpr) {
          foreach (MatchCaseExpr mc in matchExpr.Cases) {
            foreach (BoundVar v in mc.Arguments) {
              VisitUserProvidedType(v.Type, context);
            }
          }
        } else if (expr is NestedMatchExpr nestedMatchExpr) {
          foreach (var mc in nestedMatchExpr.Cases) {
            VisitExtendedPattern(mc.Pat, context);
          }
        }

        // Visit substatements
        if (expr is StmtExpr stmtExpr) {
          VisitStatement(stmtExpr.S, context);
        }

        // Visit subexpressions
        expr.SubExpressions.ForEach(ee => VisitExpression(ee, context));

        PostVisitOneExpression(expr, context);
      }
    }

    protected virtual void VisitExtendedPattern(ExtendedPattern pattern, VisitorContext context) {
      switch (pattern) {
        case DisjunctivePattern disjunctivePattern:
          foreach (var alternative in disjunctivePattern.Alternatives) {
            VisitExtendedPattern(alternative, context);
          }
          break;
        case LitPattern:
          break;
        case IdPattern idPattern:
          if (idPattern.BoundVar != null) {
            VisitUserProvidedType(idPattern.BoundVar.Type, context);
          }
          if (idPattern.Arguments != null) {
            foreach (var argument in idPattern.Arguments) {
              VisitExtendedPattern(argument, context);
            }
          }
          break;
        default:
          Contract.Assert(false); // unexpected case
          break;
      }
    }

    /// <summary>
    /// This method is called only for FrameExpression's that are part of top-level or member declarations.
    /// Some statements (modifies clauses of loops) and expressions (reads clauses of lambda expressions, unchanged expressions)
    /// also have FrameExpression's, but the ASTVisitor does not automatically call VisitTopLevelFrameExpression on those, only
    /// VisitExpression.
    /// </summary>
    public virtual void VisitTopLevelFrameExpression(FrameExpression frameExpression, VisitorContext context) {
      VisitExpression(frameExpression.E, context);
    }

    /// <summary>
    /// Visits the given expression.
    /// Returns "true" to request that the caller
    ///   - keeps visiting all user-provided types, subexpressions, and substatements of "expr", and
    ///   - then calls PostVisitOneExpression.
    /// Returns "false" to tell the caller not to do those things.
    /// </summary>
    protected virtual bool VisitOneExpression(Expression expr, VisitorContext context) {
      return true;
    }

    protected virtual void PostVisitOneExpression(Expression expr, VisitorContext context) {
    }

    protected virtual void VisitStatement(Statement stmt, VisitorContext context) {
      if (VisitOneStatement(stmt, context)) {
        // Visit user-provided types
        if (stmt is VarDeclStmt varDeclStmt) {
          foreach (var local in varDeclStmt.Locals) {
            VisitUserProvidedType(local.SyntacticType, context);
          }

        } else if (stmt is VarDeclPattern varDeclPattern) {
          foreach (var local in varDeclPattern.LocalVars) {
            VisitUserProvidedType(local.SyntacticType, context);
          }

        } else if (stmt is SingleAssignStmt assignStmt) {
          if (assignStmt.Rhs is TypeRhs typeRhs) {
            if (typeRhs.EType != null) {
              VisitUserProvidedType(typeRhs.EType, context);
            }
          }

        } else if (stmt is OneBodyLoopStmt oneBodyLoopStmt) {
          if (oneBodyLoopStmt is ForLoopStmt forLoopStmt) {
            VisitUserProvidedType(forLoopStmt.LoopIndex.Type, context);
          }

        } else if (stmt is ForallStmt forallStmt) {
          foreach (BoundVar v in forallStmt.BoundVars) {
            VisitUserProvidedType(v.Type, context);
          }

        } else if (stmt is NestedMatchStmt nestedMatchStmt) {
          foreach (var mc in nestedMatchStmt.Cases) {
            VisitExtendedPattern(mc.Pat, context);
          }

        } else if (stmt is MatchStmt matchStmt) {
          foreach (MatchCaseStmt mc in matchStmt.Cases) {
            if (mc.Arguments != null) {
              foreach (BoundVar v in mc.Arguments) {
                VisitUserProvidedType(v.Type, context);
              }
            }
          }
        }

        // Visit subexpressions
        stmt.SubExpressions.ForEach(ee => VisitExpression(ee, context));

        // Visit substatements
        stmt.SubStatements.ForEach(ss => VisitStatement(ss, context));

        PostVisitOneStatement(stmt, context);
      }
    }

    /// <summary>
    /// Visits the given statement.
    /// Returns "true" to request that the caller
    ///   - keeps visiting all user-provided types, subexpressions, and substatements of "stmt", and
    ///   - then calls PostVisitOneStatement.
    /// Returns "false" to tell the caller not to do those things.
    /// </summary>
    protected virtual bool VisitOneStatement(Statement stmt, VisitorContext context) {
      return true;
    }

    protected virtual void PostVisitOneStatement(Statement stmt, VisitorContext context) {
    }
  }

}
