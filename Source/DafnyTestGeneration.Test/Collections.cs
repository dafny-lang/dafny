using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace DafnyTestGeneration.Test {

  [TestClass]
  public class Collections {

    [TestInitialize]
    public void SetupDafnyOptions() {
      Setup.SetupDafnyOptions();
    }

    [TestMethod]
    public async Task StringLength() {
      var source = @"
class C {
  static method compareStringLengthToOne(s: string) returns (ret: int) {
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
      var program = Utils.Parse(source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.AreEqual(3, methods.Count);
      Assert.IsTrue(methods.All(m =>
        m.MethodName == "C.compareStringLengthToOne"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("C.compareStringLengthToOne")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "[]"));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\\['.'\\]")));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\\['.'(, '.')+\\]")));
    }

    [TestMethod]
    public async Task SeqOfObjects() {
      var source = @"
class CharObject {
   var value:char;
}

class SimpleTest {
  static method compareStringToSeqOfChars(s: string, c:seq<CharObject>)
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
      var program = Utils.Parse(source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      // Assert.AreEqual(3, methods.Count);
      Assert.IsTrue(methods.All(m =>
        m.MethodName ==
        "SimpleTest.compareStringToSeqOfChars"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic(
          "SimpleTest.compareStringToSeqOfChars")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 2));
      Assert.IsTrue(methods.All(m =>
        Regex.IsMatch(m.ArgValues[0], "\\['.'(, '.')*\\]") ||
        m.ArgValues[0] == "[]"));
      Assert.IsTrue(methods.All(m =>
        Regex.IsMatch(m.ArgValues[1],
          "\\[(v[0-9]+|null)(, (v[0-9]+|null))*\\]") ||
        m.ArgValues[1] == "[]"));

      Assert.IsTrue(methods.Exists(m =>
        m.ArgValues[0].Split(",").Length != m.ArgValues[1].Split(",").Length));

      Assert.IsTrue(methods.Exists(m =>
        m.ArgValues[0].Split(",").Length < 2 &&
        m.ArgValues[0].Split(",").Length == m.ArgValues[1].Split(",").Length));
    }

  }
}