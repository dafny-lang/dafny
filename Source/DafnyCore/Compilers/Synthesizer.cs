using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.Compilers;

/// <summary>
/// Base class for synthesizers. Uses ensures clauses to specify
/// the behavior of an object returned by a synthesize-annotated method. 
/// </summary>
public abstract class Synthesizer {

  protected SinglePassCompiler compiler;
  protected ConcreteSyntaxTree errorWriter;
  // maps identifiers to the names of the corresponding mock:
  protected Dictionary<IVariable, string> objectToMockName = new();
  // associates a bound variable with the lambda passed to argument matcher
  protected Dictionary<IVariable, string> bounds = new();
  protected Method lastSynthesizedMethod = null;

  /// <summary>
  /// Create a body of a method that synthesizes one or more objects.
  /// </summary>
  public abstract ConcreteSyntaxTree SynthesizeMethod(Method method,
    List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody,
    ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody);

  /// <summary>
  /// If the expression is a bound variable identifier, return the
  /// variable and the string representation of the bounding condition
  /// </summary>
  protected Tuple<IVariable, string> GetBound(Expression exp) {
    if (exp is not NameSegment) {
      return null;
    }
    var variable = ((IdentifierExpr)exp.Resolved).Var;
    if (!bounds.ContainsKey(variable)) {
      return null;
    }
    return new Tuple<IVariable, string>(variable, bounds[variable]);
  }

  protected void SynthesizeExpression(ConcreteSyntaxTree wr, Expression expr, ConcreteSyntaxTree wStmts) {
    switch (expr) {
      case LiteralExpr literalExpr:
        compiler.TrExpr(literalExpr, wr, false, wStmts);
        break;
      case ApplySuffix applySuffix:
        SynthesizeExpression(wr, applySuffix, wStmts);
        break;
      case BinaryExpr binaryExpr:
        SynthesizeExpression(wr, binaryExpr, wStmts);
        break;
      case ForallExpr forallExpr:
        SynthesizeExpression(wr, forallExpr, wStmts);
        break;
      case FreshExpr:
        break;
      default:
        // TODO: Have the resolver reject all these unimplemented cases,
        // or convert them to UnsupportedFeatureExceptions
        throw new NotImplementedException();
    }
  }

  protected abstract void SynthesizeExpression(ConcreteSyntaxTree wr, ApplySuffix applySuffix, ConcreteSyntaxTree wStmts);
  protected abstract void SynthesizeExpression(ConcreteSyntaxTree wr, BinaryExpr binaryExpr, ConcreteSyntaxTree wStmts);
  protected abstract void SynthesizeExpression(ConcreteSyntaxTree wr, ForallExpr forallExpr, ConcreteSyntaxTree wStmts);
}