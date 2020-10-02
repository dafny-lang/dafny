using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using DafnyTests;
using Xunit.Abstractions;
using Xunit.Sdk;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.RepresentationModel;
using YamlDotNet.Serialization;

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