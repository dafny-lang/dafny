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
      var (testCases, testContent) = convertor.ConvertLitCommands("TestFiles", "TestFiles/HelloWorldLitTest.dfy", false, lines);
    }
 
    [Fact]
    public void VerifyOnly() {
      var convertor = new LitTestConvertor();
      using var stream =
        Assembly.GetExecutingAssembly().GetManifestResourceStream("LitTestConvertor.Test.TestFiles.VerifyOnlyLitTest.dfy");
      using var reader = new StreamReader(stream);
      var lines = File.ReadLines("TestFiles/VerifyOnly.dfy");
      var (testCases, testContent) = convertor.ConvertLitCommands("TestFiles", "TestFiles/VerifyOnly.dfy", false, lines);
    }
  }
}