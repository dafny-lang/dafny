using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;

namespace DafnyDriver.Test {
  public class LitTestDataDiscoverer : FileDataDiscoverer {

    private readonly LitTestConverter.LitTestConvertor convertor = new();

    public override bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }

    protected override IEnumerable<object[]> FileData(IAttributeInfo attributeInfo, IMethodInfo testMethod, string fileName) {
      bool invokeDirectly = attributeInfo.GetNamedArgument<bool>(nameof(LitTestDataAttribute.InvokeCliDirectly));
      try {
        var (testCases, _) = convertor.ConvertLitCommands(GetBasePath(attributeInfo, testMethod), fileName, invokeDirectly, File.ReadLines(fileName));
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
  public bool InvokeCliDirectly;
  public LitTestDataAttribute(bool invokeCliDirectly = false) : base(extension: ".dfy") {
    InvokeCliDirectly = invokeCliDirectly;
  }
}