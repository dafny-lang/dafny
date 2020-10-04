using System;
using System.Collections.Generic;
using System.Reflection;
using Xunit.Sdk;

namespace XUnitExtensions {
  
  [DataDiscoverer("XUnitExtensions.YamlDataDiscoverer", "DafnyTests")]
  public class YamlDataAttribute : DataAttribute {

    public YamlDataAttribute(bool withParameterNames = true) {
    }
    
    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      throw new NotImplementedException();
    }
  }
}