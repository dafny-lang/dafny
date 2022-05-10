using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.Dafny;


[TestClass]
public class TestExperiment {

  [TestMethod]
  public void DaTest() {
    RealThing(2).Run();
  }

  private async DynamicStack RealThing(int iterations) {
    Console.WriteLine("Before " + iterations);
    if (iterations > 0) {
      await RealThing2(iterations - 1);
    }
    Console.WriteLine("After " + iterations);
  }

  private async DynamicStack RealThing2(int iterations) {
    Console.WriteLine("Before " + iterations);
    if (iterations > 0) {
      await RealThing(iterations - 1);
    }
    Console.WriteLine("After2 " + iterations);
  }
  
  [TestMethod]
  public void BoomTest() {
    Boom(100_000);
  }
  private void Boom(int iterations) {
    if (iterations > 0) {
      Boom(iterations - 1);
    }
  }


  [TestMethod]
  public void TaskBoomTest() {
    TaskBoom(100_000).Wait();
  }
  private async Task TaskBoom(int iterations) {
    if (iterations > 0) {
      await TaskBoom(iterations - 1).ConfigureAwait(false);
    }
  }
}