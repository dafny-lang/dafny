using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit.Abstractions;
using Xunit.Sdk;
using XUnitExtensions;

namespace XUnitExtensions {
  public class LitTestDataDiscoverer : FileDataDiscoverer {

    public override bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod) {
      return true;
    }

    protected override IEnumerable<object[]> FileData(IAttributeInfo attributeInfo, IMethodInfo testMethod, string fileName) {
      var basePath = GetBasePath(attributeInfo, testMethod);
      var shortPath = fileName[(basePath.Length + 1)..];
      var row = new FileTheoryDataRow(fileName) {
        SourceInformation = new SourceInformation() { FileName = fileName, LineNumber = 0 },
        TestDisplayName = shortPath,
      };
      return new[] { new[] { row } };
    }
  }
}

[DataDiscoverer("XUnitExtensions.LitTestDataDiscoverer", "XUnitExtensions")]
public class LitTestDataAttribute : FileDataAttribute {

}