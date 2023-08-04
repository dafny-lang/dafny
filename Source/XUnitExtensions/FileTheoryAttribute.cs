using System;
using Xunit;
using Xunit.Sdk;

namespace XUnitExtensions {
  [AttributeUsage(AttributeTargets.Method)]
  [XunitTestCaseDiscoverer("XUnitExtensions.FileTheoryDiscoverer", "XUnitExtensions")]
  public class FileTheoryAttribute : TheoryAttribute {
  }
}