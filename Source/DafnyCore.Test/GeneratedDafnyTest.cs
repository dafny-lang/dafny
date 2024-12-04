using System.Collections.Concurrent;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class GeneratedDafnyTest {
  [Fact]
  public void TestDafnyCoverage() {
    DafnyToRustCompilerCoverage.__default.TestIsCopy(); ;
  }

  [Fact]
  public void TestRustASTCoverage() {
    RASTCoverage.__default.TestExpr();
  }

  [Fact]
  public void TestPathSimplification() {
    FactorPathsOptimizationTest.__default.TestApply();
  }

  [Fact]
  public void TestDefsCoverage() {
    DefsCoverage.__default.Tests();
  }
}