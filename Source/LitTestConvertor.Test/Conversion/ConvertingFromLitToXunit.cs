using System.Collections.Generic;
using System.IO;
using System.Reflection;
using Xunit;
using XUnitExtensions;

namespace LitTestConvertor.Test {
  public class ConvertingFromLitToXunit {

    [Fact]
    public void HelloWorld() {
      var config = new LitTestConfiguration();
      var program = LitTestCase.Read("TestFiles/HelloWorldLitTest.dfy", config);
    }

    [Fact]
    public void VerifyOnly() {
      var config = new LitTestConfiguration();
      var program = LitTestCase.Read("TestFiles/VerifyOnly.dfy", config);
    }
  }
}