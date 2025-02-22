using System.Collections;
using System.Collections.Generic;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class StringifyTest {

  record Inner(int Age, string Name);

  record Outer(Inner[] InnersArray, IDictionary<string, Inner> MoreInners);

  [Fact]
  public void StringifyThing() {
    var outer = new Outer([new Inner(3, "Jan"), new Inner(4, "Jaap")],
      new Dictionary<string, Inner>() {
        { "Marie", new Inner(5, "Antoinette") },
      });
    var result = outer.Stringify();
    Assert.Equal(@"
Outer {
  InnersArray = [
    Inner {
      Age = 3,
      Name = ""Jan""
    }, 
    Inner {
      Age = 4,
      Name = ""Jaap""
    }
  ],
  MoreInners = [
    {
      Key = ""Marie"",
      Value = Inner {
        Age = 5,
        Name = ""Antoinette""
      }
    }
  ]
}".TrimStart(), result);
  }
}