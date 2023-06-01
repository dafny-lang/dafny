// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Linq.Expressions;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class BitvectorOptimization : IRewriter {
  private readonly BuiltIns builtIns;
  public BitvectorOptimization(BuiltIns builtIns, ErrorReporter reporter) : base(reporter) {
    this.builtIns = builtIns;
  }

  internal override void PostResolveIntermediate(Resolver resolver, ModuleDefinition m) {
    var visitor = new BitvectorOptimizationVisitor(Reporter.Options, builtIns);
    foreach (var decl in ModuleDefinition.AllItersAndCallables(m.TopLevelDecls)) {
      visitor.Visit(decl);
    }
  }
}

public class BitvectorOptimizationVisitor : BottomUpVisitor {
  private readonly DafnyOptions options;
  private readonly BuiltIns builtIns;

  public BitvectorOptimizationVisitor(DafnyOptions options, BuiltIns builtIns) {
    this.options = options;
    this.builtIns = builtIns;
  }

  private bool IsShiftOp(BinaryExpr.Opcode op) {
    return op is BinaryExpr.Opcode.LeftShift or BinaryExpr.Opcode.RightShift;
  }

  private Expression ShrinkBitVectorShiftAmount(Expression expr, BitvectorType originalType) {
    var width = new BigInteger(originalType.Width);
    var intermediateType = new BitvectorType(options, (int)width.GetBitLength());
    builtIns.Bitwidths.Add(intermediateType.Width);
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