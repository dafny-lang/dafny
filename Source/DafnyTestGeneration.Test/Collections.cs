using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test {

  public class Collections : Setup {
    private readonly ITestOutputHelper testOutputHelper;

    public Collections(ITestOutputHelper testOutputHelper) {
      this.testOutputHelper = testOutputHelper;
    }

    [Theory(Skip = "Implementation doesn't always return correct results on Windows CI, https://github.com/dafny-lang/dafny/issues/3828")]
    [MemberData(nameof(OptionSettings))]
    private async Task StringLength(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module C {
  method compareStringLengthToOne(s: string) returns (ret: int) {
      if (|s| == 1) {
          return 0;
      } else if (|s| > 1) {
          return 1;
      } else {
          return -1;
      }
  }
}

".TrimStart();
      var program = Utils.Parse(GetDafnyOptions(optionSettings, new WriterFromOutputHelper(testOutputHelper)), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(3, methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName == "C.compareStringLengthToOne"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("C.compareStringLengthToOne")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 1));
      Assert.True(methods.Exists(m => m.ValueCreation[0].value == "\"\""));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ValueCreation[0].value, "\".\"")));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ValueCreation[0].value, "\"..+\"")));
    }

    [Theory(Skip = "Implementation doesn't always return correct results on Windows CI, https://github.com/dafny-lang/dafny/issues/3828")]
    [MemberData(nameof(OptionSettings))]
    private async Task SeqOfObjects(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {

  class CharObject {
     var value:char;
  }

  method compareStringToSeqOfChars(s: string, c:seq<CharObject>)
      returns (ret: bool)
  {
      if ((|s| != |c|) || (|s| < 2)) {
          return false;
      }
      var i: int := |c| - 1;
      while (i >= 0)
          decreases i
          invariant i >= -1
          invariant i < |c| {
          if (s[i] != c[i].value) {
              return false;
          }
          i := i - 1;
      }
      return true;
  }
}
".TrimStart();
      var program = Utils.Parse(GetDafnyOptions(optionSettings, new WriterFromOutputHelper(testOutputHelper)), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      if (methods.Count != 3) { // This sometimes occurs on Windows
        testOutputHelper.WriteLine("methods.Count != 3, printing methods");
        foreach (var method in methods) {
          testOutputHelper.WriteLine(method.ToString());
        }
      }

      Assert.Equal(3, methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName ==
        "SimpleTest.compareStringToSeqOfChars"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic(
          "SimpleTest.compareStringToSeqOfChars")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m =>
        Regex.IsMatch(m.ValueCreation[0].value, "\".*\"")));
      Assert.True(methods.All(m =>
        Regex.IsMatch(m.ValueCreation.Last().value,
          "\\[(charObject[0-9]+|null)(, (charObject[0-9]+|null))*\\]") ||
        m.ValueCreation[1].value == "[]"));

      Assert.True(methods.Exists(m =>
        m.ValueCreation[0].value.Length - 2 !=
        m.ValueCreation.Last().value.Split(",").Length));

      Assert.True(methods.Exists(m =>
        m.ArgValues[0].Split(",").Length < 2));
      // This test is too specific. A test input may be valid and still not satisfy it.
      /*
      Assert.True(methods.Exists(m =>
        m.ValueCreation[0].value.Length < 4 &&
        m.ValueCreation[0].value.Length - 2 ==
        m.ValueCreation.Last().value.Split(",").Length));*/
    }

  }
}
