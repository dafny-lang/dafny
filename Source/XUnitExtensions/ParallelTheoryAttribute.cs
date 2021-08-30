using System;
using Xunit;
using Xunit.Sdk;

[AttributeUsage(AttributeTargets.Method)]
[XunitTestCaseDiscoverer("XUnitExtensions.CollectionPerTestCaseTheoryDiscoverer", "DafnyDriver.Test")]
public class ParallelTheoryAttribute : TheoryAttribute { }