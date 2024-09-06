using System.Collections.Concurrent;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class GeneratedDafnyTest {
  [Fact]
  public void TestDafnyCoverage() {
    DafnyToRustCompilerCoverage.RASTCoverage.__default.TestExpr();
  }
  
  [Fact]
  public void TestPathSimplification() {
    FactorPathsOptimizationTest.__default.TestApply();
  }
}