using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;

namespace Microsoft.Dafny;

public static class FuelAdjustment {

  public static void CheckForFuelAdjustments(ErrorReporter reporter, ModuleDefinition module) {
    CheckForFuelAdjustments(reporter, module.Origin, module.Attributes, module);
    foreach (var clbl in ModuleDefinition.AllItersAndCallables(module.TopLevelDecls)) {
      Statement body = null;
      if (clbl is MethodOrConstructor method) {
        body = method.Body;
        CheckForFuelAdjustments(reporter, clbl.Origin, method.Attributes, module);
      } else if (clbl is IteratorDecl iteratorDecl) {
        body = iteratorDecl.Body;
        CheckForFuelAdjustments(reporter, clbl.Origin, iteratorDecl.Attributes, module);
      } else if (clbl is Function function) {
        CheckForFuelAdjustments(reporter, clbl.Origin, function.Attributes, module);
        var c = new FuelAdjustmentVisitor(reporter);
        var bodyExpr = function.Body;
        if (bodyExpr != null) {
          c.Visit(bodyExpr, new FuelAdjustmentContext(module));
        }
      }

      if (body != null) {
        var c = new FuelAdjustmentVisitor(reporter);
        c.Visit(body, new FuelAdjustmentContext(module));
      }
    }
  }

  public static void CheckForFuelAdjustments(ErrorReporter reporter, IOrigin tok, Attributes attrs, ModuleDefinition currentModule) {
    List<List<Expression>> results = Attributes.FindAllExpressions(attrs, "fuel");

    if (results == null) {
      return;
    }

    foreach (var args in results) {
      if (args == null || args.Count < 2) {
        continue;
      }

      // Try to extract the function from the first argument
      var selectExpr = args[0].Resolved as MemberSelectExpr;

      if (selectExpr?.Member is not Function function) {
        continue;
      }

      function.IsFueled = true;
      if (args.Count < 3) {
        continue;
      }

      if (args[1] is not LiteralExpr { Value: BigInteger low } ||
          args[2] is not LiteralExpr { Value: BigInteger high }) {
        continue;
      }

      if (!(high == low + 1 || (low == 0 && high == 0))) {
        reporter.Error(MessageSource.Resolver, tok, "fuel setting for function {0} must have high value == 1 + low value", function.Name);
      }
    }
  }
}

class FuelAdjustmentVisitor : ResolverTopDownVisitor<FuelAdjustmentContext> {

  public FuelAdjustmentVisitor(ErrorReporter reporter)
    : base(reporter) {
  }

  protected override bool VisitOneStmt(Statement stmt, ref FuelAdjustmentContext st) {
    FuelAdjustment.CheckForFuelAdjustments(reporter, stmt.Origin, stmt.Attributes, st.currentModule);
    return true;
  }
}


public class FuelAdjustmentContext {
  public ModuleDefinition currentModule;
  public FuelAdjustmentContext(ModuleDefinition currentModule) {
    this.currentModule = currentModule;
  }
}