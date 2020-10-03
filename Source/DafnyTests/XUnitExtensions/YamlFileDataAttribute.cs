using System;
using System.Collections.Generic;
using System.Reflection;
using Xunit.Sdk;

namespace XUnitExtensions {
  
  [DataDiscoverer("XUnitExtensions.YamlFileDataDiscoverer", "DafnyTests")]
  public class YamlFileDataAttribute : DataAttribute {

    public YamlFileDataAttribute(string rootPath, bool withParameterNames = true) {
    }
    
    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      throw new NotImplementedException();
    }
  }
}