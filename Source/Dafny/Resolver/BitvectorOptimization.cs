// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Linq.Expressions;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class BitvectorOptimization : IRewriter {
  public BitvectorOptimization(ErrorReporter reporter) : base(reporter) { }

  internal override void PostResolveIntermediate(ModuleDefinition m) {
    var visitor = new BitvectorOptimizationVisitor();
    foreach (var decl in ModuleDefinition.AllItersAndCallables(m.TopLevelDecls)) {
      visitor.Visit(decl);
    }
  }
}

public class BitvectorOptimizationVisitor : BottomUpVisitor {
  private bool IsShiftOp(BinaryExpr.Opcode op) {
    return op is BinaryExpr.Opcode.LeftShift or BinaryExpr.Opcode.RightShift;
  }

  private Expression ShrinkBitVectorShiftAmount(Expression expr, BitvectorType originalType) {
    var width = new BigInteger(originalType.Width);
    var intermediateType = new BitvectorType((int)width.GetBitLength());
    var newExpr = new ConversionExpr(expr.tok, expr, intermediateType, "when converting shift amount to a bit vector, the ");
    newExpr.Type = intermediateType;
    return newExpr;
  }

  protected override void VisitOneExpr(Expression expr) {
    if (expr.Type is BitvectorType bvType) {

      if (expr is BinaryExpr binExpr && IsShiftOp(binExpr.Op)) {
        binExpr.E1 = ShrinkBitVectorShiftAmount(binExpr.E1, bvType);
      }
    }
  }
}