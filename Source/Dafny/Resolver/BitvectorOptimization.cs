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
    foreach (var decl in ModuleDefinition.AllCallables(m.TopLevelDecls)) {
      visitor.Visit(decl);
    }
  }
}

public class BitvectorOptimizationVisitor : BottomUpVisitor {
  private bool IsShift(BinaryExpr.Opcode op) {
    return op is BinaryExpr.Opcode.LeftShift or BinaryExpr.Opcode.RightShift;
  }
  protected override void VisitOneExpr(Expression expr) {
    // TODO: rotate, too
    if (expr is BinaryExpr binExpr && IsShift(binExpr.Op) && binExpr.Type is BitvectorType bvType) {
      var width = new BigInteger(bvType.Width);
      var intermediateType = new BitvectorType((int)width.GetBitLength());
      binExpr.E1 = new ConversionExpr(binExpr.E1.tok, binExpr.E1, intermediateType);
      binExpr.E1.Type = intermediateType;
    }
  }
}