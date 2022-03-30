using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace DafnyTestGeneration.Test {

  [TestClass]
  public class BasicTypes {

    [TestInitialize]
    public void SetupDafnyOptions() {
      Setup.SetupDafnyOptions();
    }

    [TestMethod]
    public async Task Ints() {
      var source = @"
class SimpleTest {
  static method compareToZero(i: int) returns (ret: int) {
    if (i == 0) {
        return 0;
    } else if (i > 0) {
        return 1;
    }
    return -1;
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.AreEqual(3, methods.Count);
      Assert.IsTrue(methods.All(m =>
        m.MethodName == "SimpleTest.compareToZero"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToZero")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "0"));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "-[1-9][0-9]*")));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "[1-9][0-9]*")));
    }

    [TestMethod]
    public async Task Bools() {
      var source = @"
class SimpleTest {
  static method checkIfTrue(b: bool) returns (ret: bool) {
    if (b) {
        return true;
    }
    return false;
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.AreEqual(2, methods.Count);
      Assert.IsTrue(methods.All(m => m.MethodName == "SimpleTest.checkIfTrue"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.checkIfTrue")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "false"));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "true"));
    }

    [TestMethod]
    public async Task Reals() {
      var source = @"
class SimpleTest {
  static method compareToZero(r: real) returns (ret: int) {
    if (r == 0.0) {
        return 0;
    } else if ((r > 0.0) && (r < 1.0)) {
        return 1;
    } else if ((r < 0.0) && (r > -1.0)){
        return -1;
    } else if (r == 1.0) {
        return 1;
    } else if (r == -1.0) {
        return -1;
    } else if (r > 0.0) {
        return 1;
    }
    return -1;
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.AreEqual(7, methods.Count);
      Assert.IsTrue(
        methods.All(m => m.MethodName == "SimpleTest.compareToZero"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToZero")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "0.0"));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "1.0"));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "-1.0"));
      Assert.IsTrue(methods.Exists(m => Regex.IsMatch(m.ArgValues[0],
        "-[1-9][0-9]*\\.[0-9]*/[1-9][0-9]*\\.[0-9]*")));
      Assert.IsTrue(methods.Exists(m => Regex.IsMatch(m.ArgValues[0],
        "[1-9][0-9]*\\.[0-9]*/[1-9][0-9]*\\.[0-9]*")));
    }

    [TestMethod]
    public async Task BitVectors() {
      var source = @"
class SimpleTest {
  static method compareToBase(r: bv10) returns (ret: int) {
    if (r == (10 as bv10)) {
        return 0;
    } else if (r > (10 as bv10)) {
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
      Assert.IsTrue(
        methods.All(m => m.MethodName == "SimpleTest.compareToBase"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToBase")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "(10 as bv10)"));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\\([0-9] as bv10\\)")));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\\([1-9][0-9]+ as bv10\\)")));
    }

    [TestMethod]
    public async Task Chars() {
      var source = @"
class SimpleTest {
  static method compareToB(c: char) returns (ret: int) {
    if (c == 'B') {
        return 0;
    } else if (c > 'B') {
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
      Assert.IsTrue(methods.All(m => m.MethodName == "SimpleTest.compareToB"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToB")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "'B'"));
      Assert.IsTrue(methods.Exists(m =>
        m.ArgValues[0].Length == 3 && m.ArgValues[0][1] > 'B'));
      Assert.IsTrue(methods.Exists(m =>
        m.ArgValues[0].Length == 3 && m.ArgValues[0][1] < 'B'));
    }

    [TestMethod]
    public async Task CharsUnspecified() {
      // This test case is different from the one above because the model would
      // not specify the exact value of c when the only constraint on it is that
      // c != 'B"
      var source = @"
class SimpleTest {
  static method compareToB(c: char) returns (b:bool) {
    if (c == 'B') {
      return false;
    } else {
      return true;
    }
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.AreEqual(2, methods.Count);
      Assert.IsTrue(methods.All(m => m.MethodName == "SimpleTest.compareToB"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToB")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[0] == "'B'"));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "'[^B]'")));
    }

  }
}
