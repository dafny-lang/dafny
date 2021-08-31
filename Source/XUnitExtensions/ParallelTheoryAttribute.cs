using System;
using Xunit;
using Xunit.Sdk;

namespace XUnitExtensions {
  [AttributeUsage(AttributeTargets.Method)]
  [XunitTestCaseDiscoverer("XUnitExtensions.CollectionPerTestCaseTheoryDiscoverer", "XUnitExtensions")]
  public class ParallelTheoryAttribute : TheoryAttribute {
  }
}