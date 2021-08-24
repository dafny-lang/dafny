using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Dafny;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace DafnyTestGeneration.Test {


  [TestClass]
  public class Varia {

    [TestInitialize]
    public void SetupDafnyOptions() {
      Setup.SetupDafnyOptions();
    }

    [TestMethod]
    public void NoInlining() {
      var source = @"
class Inlining {
  method b (i:int) returns (r:int) {
    if (i == 0) {
        return 7;
    } else {
        return 81;
    }
  }
  method a (i:int) returns (r:int) {
    r := b(i);
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      var methods = Main.GetTestMethodsForProgram(program).ToList();
      Assert.AreEqual(3, methods.Count);
      Assert.AreEqual(2, methods.Count(m => m.MethodName == "Inlining.b"));
      Assert.AreEqual(1, methods.Count(m => m.MethodName == "Inlining.a"));
      Assert.IsTrue(methods.All(m => !m.DafnyInfo.IsStatic("Inlining.b")));
      Assert.IsTrue(methods.All(m => !m.DafnyInfo.IsStatic("Inlining.a")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 2));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 1));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[1] == "0"));
      Assert.IsTrue(methods.Count(m => m.ArgValues[1] != "0") is 1 or 2);
      Assert.IsTrue(methods.All(m =>
        Regex.IsMatch(m.ArgValues[1], "-?[0-9]+")));
    }

    [TestMethod]
    public void Inlining() {
      var source = @"
class Inlining {
  method b (i:int) returns (r:int) {
    if (i == 0) {
        return 7;
    } else {
        return 81;
    }
  }
  method a (i:int) returns (r:int) {
    r := b(i);
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      DafnyOptions.O.MethodToTest = "Inlining.a";
      DafnyOptions.O.TestInlineDepth = 1;
      var methods = Main.GetTestMethodsForProgram(program).ToList();
      Assert.AreEqual(2, methods.Count);
      Assert.IsTrue(methods.All(m => m.MethodName == "Inlining.a"));
      Assert.IsTrue(methods.All(m => !m.DafnyInfo.IsStatic("Inlining.a")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 2));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 1));
      Assert.IsTrue(methods.Exists(m => m.ArgValues[1] == "0"));
      Assert.IsTrue(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[1], "-?[1-9][0-9]*")));
    }

    [TestMethod]
    public void PathBasedTests() {
      var source = @"
class Paths {
  static method eightPaths (i:int)
    returns (divBy2:bool, divBy3:bool, divBy5:bool)
  {
		if (i % 2 == 0) {
			divBy2 := true;
		} else {
			divBy2 := false;
		}
		if (i % 3 == 0) {
      divBy3 := true;
    } else {
      divBy3 := false;
    }
    if (i % 5 == 0) {
      divBy5 := true;
    } else {
      divBy5 := false;
    }
	}
}
".TrimStart();
      var program = Utils.Parse(source);
      DafnyOptions.O.TestMode = DafnyOptions.TestModes.Path;
      var methods = Main.GetTestMethodsForProgram(program).ToList();
      Assert.AreEqual(8, methods.Count);
      Assert.IsTrue(methods.All(m => m.MethodName == "Paths.eightPaths"));
      Assert.IsTrue(methods.All(m => m.DafnyInfo.IsStatic("Paths.eightPaths")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      var values = methods.Select(m =>
          int.TryParse(m.ArgValues[0], out var result) ? (int?) result : null)
        .ToList();
      Assert.IsTrue(values.All(i => i != null));
      Assert.IsTrue(values.Exists(i => i % 2 == 0 && i % 3 == 0 && i % 5 == 0));
      Assert.IsTrue(values.Exists(i => i % 2 == 0 && i % 3 == 0 && i % 5 != 0));
      Assert.IsTrue(values.Exists(i => i % 2 == 0 && i % 3 != 0 && i % 5 == 0));
      Assert.IsTrue(values.Exists(i => i % 2 == 0 && i % 3 != 0 && i % 5 != 0));
      Assert.IsTrue(values.Exists(i => i % 2 != 0 && i % 3 == 0 && i % 5 == 0));
      Assert.IsTrue(values.Exists(i => i % 2 != 0 && i % 3 == 0 && i % 5 != 0));
      Assert.IsTrue(values.Exists(i => i % 2 != 0 && i % 3 != 0 && i % 5 == 0));
      Assert.IsTrue(values.Exists(i => i % 2 != 0 && i % 3 != 0 && i % 5 != 0));
    }

    [TestMethod]
    public void BlockBasedTests() {
      var source = @"
class Paths {
  static method eightPaths (i:int) returns (divBy2:bool, divBy3:bool, divBy5:bool) {
		if (i % 2 == 0) {
			divBy2 := true;
		} else {
			divBy2 := false;
		}
		if (i % 3 == 0) {
      divBy3 := true;
    } else {
      divBy3 := false;
    }
    if (i % 5 == 0) {
      divBy5 := true;
    } else {
      divBy5 := false;
    }
	}
}
".TrimStart();
      var program = Utils.Parse(source);
      var methods = Main.GetTestMethodsForProgram(program).ToList();
      Assert.IsTrue(methods.Count is >= 4 and <= 6);
      Assert.IsTrue(methods.All(m => m.MethodName == "Paths.eightPaths"));
      Assert.IsTrue(methods.All(m => m.DafnyInfo.IsStatic("Paths.eightPaths")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.All(m => m.ObjectsToMock.Count == 0));
      var values = methods.Select(m =>
          int.TryParse(m.ArgValues[0], out var result) ? (int?) result : null)
        .ToList();
      Assert.IsTrue(values.All(i => i != null));
      Assert.IsTrue(values.Exists(i => i % 2 == 0));
      Assert.IsTrue(values.Exists(i => i % 2 != 0));
      Assert.IsTrue(values.Exists(i => i % 3 == 0));
      Assert.IsTrue(values.Exists(i => i % 3 != 0));
      Assert.IsTrue(values.Exists(i => i % 5 == 0));
      Assert.IsTrue(values.Exists(i => i % 5 != 0));
    }

    [TestMethod]
    public void RecursivelyExtractObjectFields() {
      var source = @"
module Objects {
  class Node {
      var next: Node?;
      constructor (next2:Node) {
          next := next2;
      }
  }
  class List {
    static method IsACircleOfLessThanThree(node: Node) returns (b: bool) {
        var curr:Node? := node.next;
        var counter:int := 1;
        while ((counter < 3) && (curr != null) && (curr != node))
            invariant counter <= 3
            decreases 3 - counter {
            curr := curr.next;
            counter := counter + 1;
        }
        return curr == node;
    }
  }
}
".TrimStart();
      var program = Utils.Parse(source);
      DafnyOptions.O.MethodToTest = "Objects.List.IsACircleOfLessThanThree";
      var methods = Main.GetTestMethodsForProgram(program).ToList();
      Assert.AreEqual(3, methods.Count);
      Assert.IsTrue(methods.All(m =>
        m.MethodName == "Objects.List.IsACircleOfLessThanThree"));
      Assert.IsTrue(methods.All(m =>
        m.DafnyInfo.IsStatic("Objects.List.IsACircleOfLessThanThree")));
      Assert.IsTrue(methods.All(m => m.ArgValues.Count == 1));
      Assert.IsTrue(methods.Exists(m =>
        m.Assignments.Count == 1 && m.Assignments[0] == ("v0", "next", "v0") &&
        m.ObjectsToMock.Count == 1 ||
        m.Assignments.Count == 2 && m.Assignments[1] == ("v0", "next", "v1") &&
        m.Assignments[0] == ("v1", "next", "v0") &&
        m.ObjectsToMock.Count == 2));
      Assert.IsTrue(methods.Exists(m =>
        m.Assignments.Count > 2 && m.ObjectsToMock.Count > 2 &&
        m.Assignments.Last() == ("v0", "next", "v1") &&
        m.Assignments[^2] == ("v1", "next", "v2") ||
        m.Assignments.Count == 2 && m.ObjectsToMock.Count == 2 &&
        m.Assignments[1] == ("v0", "next", "v1") &&
        m.Assignments[0] == ("v1", "next", "v1")));
      Assert.IsTrue(methods.Exists(m =>
        m.Assignments.Count == 1 &&
        m.Assignments[0] == ("v0", "next", "null") &&
        m.ObjectsToMock.Count == 1 ||
        m.Assignments.Count == 2 && m.Assignments[1] == ("v0", "next", "v1") &&
        m.Assignments[0] == ("v1", "next", "null") &&
        m.ObjectsToMock.Count == 2));
    }

  }
}