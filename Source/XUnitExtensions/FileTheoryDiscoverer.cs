using System;
using System.Collections.Generic;
using System.Linq;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class FileTheoryDiscoverer : TheoryDiscoverer {

    public FileTheoryDiscoverer(IMessageSink diagnosticMessageSink) : base(diagnosticMessageSink) {
    }

    public override IEnumerable<IXunitTestCase> Discover(ITestFrameworkDiscoveryOptions discoveryOptions, ITestMethod testMethod, IAttributeInfo factAttribute) {
      // This discoverer requires pre-enumeration in order to assign a collection to each test case.
      discoveryOptions.SetValue("xunit.discovery.PreEnumerateTheories", true);
      return base.Discover(discoveryOptions, testMethod, factAttribute);
    }

    protected override IEnumerable<IXunitTestCase> CreateTestCasesForDataRow(ITestFrameworkDiscoveryOptions discoveryOptions, ITestMethod testMethod,
          IAttributeInfo theoryAttribute, object[] dataRow) {
      if (dataRow.Length == 1 && dataRow[0] is IFileTheoryRowData theoryRowData) {
        return new[] { new FileTestCase(DiagnosticMessageSink, testMethod, theoryRowData) };
      }

      return base.CreateTestCasesForDataRow(discoveryOptions, testMethod, theoryAttribute, dataRow);
    }
  }
}