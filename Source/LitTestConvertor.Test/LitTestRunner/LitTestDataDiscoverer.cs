using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyDriver.Test.XUnitExtensions;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace DafnyDriver.Test {
  public class LitTestDataDiscoverer : FileDataDiscoverer
  {

    private readonly LitTestConvertor.LitTestConvertor convertor = new();
    
    public override bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }

    protected override IEnumerable<object[]> FileData(IAttributeInfo attributeInfo, IMethodInfo testMethod, string fileName) {
      string shortName = fileName[(GetBasePath(attributeInfo, testMethod).Length + 1)..];
      try {
        var (testCases, _) = convertor.ConvertLitCommands(shortName, File.ReadLines(fileName));
        return testCases.Select(testCase => new[] { testCase });
      } catch (Exception) {
        // Ignore for now
        return Enumerable.Empty<object[]>();
      }
    }
  }
}

[DataDiscoverer("DafnyDriver.Test.LitTestDataDiscoverer", "LitTestConvertor.Test")]
public class LitTestDataAttribute : FileDataAttribute {
  public LitTestDataAttribute() : base(extension: ".dfy") {
  }
}