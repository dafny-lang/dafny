using System;
using Xunit;
using Xunit.Sdk;

[AttributeUsage(AttributeTargets.Method)]
[XunitTestCaseDiscoverer("XUnitExtensions.CollectionPerTestCaseTheoryDiscoverer", "XUnitExtensions")]
public class ParallelTheoryAttribute : TheoryAttribute { }