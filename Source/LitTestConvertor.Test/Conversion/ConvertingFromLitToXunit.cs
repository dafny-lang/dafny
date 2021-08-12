using System;
using System.Collections.Generic;
using System.IO;
using System.Reflection;
using DafnyDriver.Test;
using Xunit;

namespace LitTestConvertor.Test
{
  public class ConvertingFromLitToXunit
  {
        
    
    private static IEnumerable<string> ReadLines(StreamReader reader) {
      string line;
      while ((line = reader.ReadLine()) != null) {
        yield return line;
      }
    }

    [Fact]
    public void HelloWorld() {
      var convertor = new LitTestConvertor();
      var lines = File.ReadLines("TestFiles/HelloWorldLitTest.dfy");
      var (testCases, testContent) = convertor.ConvertLitCommands("TestFiles/HelloWorldLitTest.dfy", lines);
      DafnyTestSpec spec = (DafnyTestSpec)testCases;
      Assert.Equal(3, spec.Compile);
    }
 
    [Fact]
    public void VerifyOnly() {
      var convertor = new LitTestConvertor();
      using var stream =
        Assembly.GetExecutingAssembly().GetManifestResourceStream("LitTestConvertor.Test.TestFiles.VerifyOnlyLitTest.dfy");
      using var reader = new StreamReader(stream);
      var lines = File.ReadLines("TestFiles/VerifyOnly.dfy");
      var (testCases, testContent) = convertor.ConvertLitCommands("TestFiles/VerifyOnly.dfy", lines);
      DafnyTestSpec spec = (DafnyTestSpec)testCases;
      Assert.Equal(0, spec.Compile);
    }
  }
}