using System;
using System.Linq;
using System.Reflection;
using DafnyDriver.Test;
using DafnyDriver.Test.XUnitExtensions;
using Xunit;
using Xunit.Sdk;

namespace LitTestConvertor.Test.LitTestRunner {
  public class LitTestDataDiscovererTest {

    MethodInfo GetMethodInfo(Action<CLITestCase> a)
    {
      return a.Method;
    }
    
    [Fact]
    public void Discoverer() {
      var discoverer = new LitTestDataDiscoverer();
      var test = new LitTests();
      var methodInfo = GetMethodInfo(test.LitTest);
      var method = Reflector.Wrap(GetMethodInfo(test.LitTest));
      var attribute = CustomAttributeData.GetCustomAttributes(methodInfo).First(a => a.AttributeType == typeof(LitTestDataAttribute));
      var xunitAttribute = Reflector.Wrap(attribute);
      discoverer.GetData(xunitAttribute, method);
    }
  }
}