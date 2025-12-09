// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Linq.Expressions;
using System.Numerics;

namespace Microsoft.Dafny;

/// <summary>
/// This rewriter performs two tasks:
/// 1. Optimizes bitvector shift operations by shrinking shift amounts
/// 2. Collects type information (bitvector widths and float types) needed for Boogie function generation
/// </summary>
public class BitvectorOptimization : IRewriter {
  private readonly SystemModuleManager systemModuleManager;
  public BitvectorOptimization(Program program, ErrorReporter reporter) : base(reporter) {
    systemModuleManager = program.SystemModuleManager;
  }

  internal override void PostResolveIntermediate(ModuleDefinition m) {
    var visitor = new BitvectorOptimizationVisitor(Reporter.Options, systemModuleManager);
    foreach (var decl in ModuleDefinition.AllItersAndCallables(m.TopLevelDecls)) {
      visitor.Visit(decl);
    }
  }
}

public class BitvectorOptimizationVisitor : BottomUpVisitor {
  private readonly DafnyOptions options;
  private readonly SystemModuleManager systemModuleManager;

  public BitvectorOptimizationVisitor(DafnyOptions options, SystemModuleManager systemModuleManager) {
    this.options = options;
    this.systemModuleManager = systemModuleManager;
  }

  private bool IsShiftOp(BinaryExpr.Opcode op) {
    return op is BinaryExpr.Opcode.LeftShift or BinaryExpr.Opcode.RightShift;
  }

  private Expression ShrinkBitVectorShiftAmount(Expression expr, BitvectorType originalType) {
    var width = new BigInteger(originalType.Width);
    var intermediateType = new BitvectorType(options, (int)width.GetBitLength());
    systemModuleManager.Bitwidths.Add(intermediateType.Width);
    var newExpr = new ConversionExpr(expr.Origin, expr, intermediateType, "when converting shift amount to a bit vector, the ");
    newExpr.Type = intermediateType;
    return newExpr;
  }

  protected override void VisitOneExpr(Expression expr) {
    // Collect float types for Boogie function generation
    if (expr.Type != null) {
      if (expr.Type.IsFp32Type) {
        systemModuleManager.FloatWidths.Add(32);
        systemModuleManager.Bitwidths.Add(32); // fp32 needs bv32 for int conversion
      } else if (expr.Type.IsFp64Type) {
        systemModuleManager.FloatWidths.Add(64);
        systemModuleManager.Bitwidths.Add(64); // fp64 needs bv64 for int conversion
      }
    }

    if (expr is { Type.AsBitVectorType: { } bvType }) {

      if (expr is BinaryExpr binExpr && IsShiftOp(binExpr.Op)) {
        binExpr.E1 = ShrinkBitVectorShiftAmount(binExpr.E1, bvType);
      }
    }
  }
}