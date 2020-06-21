using System;
using Xunit;
using Xunit.Sdk;

[AttributeUsage(AttributeTargets.Method)]
[XunitTestCaseDiscoverer("XUnitExtensions.CollectionPerTestCaseTheoryDiscoverer", "DafnyTests")]
public class ParallelTheoryAttribute : TheoryAttribute { }