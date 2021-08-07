using System;
using System.Collections.Generic;
using System.Reflection;
using Xunit.Sdk;

namespace XUnitExtensions {
  
  [DataDiscoverer("XUnitExtensions.YamlDataDiscoverer", "DafnyDriver.Test")]
  public class YamlDataAttribute : DataAttribute {

    public YamlDataAttribute(bool withParameterNames = true) {
    }
    
    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      // This method is not used - the YamlDataDiscoverer has all of the actual logic instead
      // because it exposes some methods for subclasses to customize such as GetYamlParser.
      throw new NotImplementedException();
    }
  }
}