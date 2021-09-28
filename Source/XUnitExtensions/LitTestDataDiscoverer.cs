using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;

namespace DafnyDriver.Test {
  public class LitTestDataDiscoverer : FileDataDiscoverer {

    public override bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }

    protected override IEnumerable<object[]> FileData(IAttributeInfo attributeInfo, IMethodInfo testMethod, string fileName) {
      var invokeDirectly = attributeInfo.GetNamedArgument<bool>(nameof(LitTestDataAttribute.InvokeCliDirectly));
      var basePath = GetBasePath(attributeInfo, testMethod);
      try {
        var (testCases, _) = convertor.ConvertLitCommands(basePath, fileName, invokeDirectly, File.ReadLines(fileName));
        return testCases.Select(testCase => new[] { testCase });
      } catch (Exception e) {
        var shortPath = fileName[(basePath.Length + 1)..];
        var skippedCase = new FileTheoryDataRow(shortPath) {
          SourceInformation = new SourceInformation() { FileName = fileName, LineNumber = 0},
          TestDisplayName = shortPath,
          Skip = $"Exception: {e}"
        };
        return new[] { new[] { skippedCase } };
      }
    }
  }
}

[DataDiscoverer("DafnyDriver.Test.LitTestDataDiscoverer", "LitTestConvertor.Test")]
public class LitTestDataAttribute : FileDataAttribute {
  public bool InvokeCliDirectly { get; set; }
}