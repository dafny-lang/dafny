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
    
    private static DafnyTestSpec SpecForFileName(string fileName) {
      string filePath = fileName.Substring("TestFiles/DafnyTests/Test".Length + 1);
      return new DafnyTestSpec(filePath);
    }

    public override bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }

    protected override IEnumerable<object[]> FileData(IAttributeInfo attributeInfo, IMethodInfo testMethod, string fileName) {
      try {
        var (testCases, _) = convertor.ConvertLitCommands(fileName, File.ReadLines(fileName));
        return testCases.Select(testCase => new[] { testCase });
      } catch (Exception e) {
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