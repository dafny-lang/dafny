using System;
using System.Collections.Generic;
using System.Reflection;
using Xunit.Sdk;

namespace XUnitExtensions {
  
  [DataDiscoverer("DafnyDriver.Test.XUnitExtensions.YamlDataDiscoverer", "DafnyDriver.Test")]
  public class YamlDataAttribute : DataAttribute
  {
    public readonly bool WithParameterNames;
    
    public YamlDataAttribute(bool withParameterNames = true) {
      WithParameterNames = withParameterNames;
    }
    
    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      // This method is not used - the YamlDataDiscoverer has all of the actual logic instead
      // because it exposes some methods for subclasses to customize such as GetYamlParser.
      throw new NotImplementedException();
    }
  }
}