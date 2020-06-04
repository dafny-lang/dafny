using System;
using Xunit;
using Xunit.Sdk;

[AttributeUsage(AttributeTargets.Method)]
[XunitTestCaseDiscoverer("XUnitExtensions.CollectionPerTestCaseTheoryDiscoverer", "DafnyTests-NetCore")]
public class ParallelTheoryAttribute : TheoryAttribute { }