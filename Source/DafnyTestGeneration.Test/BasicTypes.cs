using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.IntegrationTest;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test {

  public class BasicTypes {
    private readonly TextWriter output;

    public BasicTypes(ITestOutputHelper output)
    {
      this.output = new WriterFromOutputHelper(output);
    }

    [Fact]
    public async Task Ints() {
      var source = @"
module SimpleTest {
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
      var options = Setup.GetDafnyOptions(output);
      var program = Utils.Parse(options, source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(3, methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName == "SimpleTest.compareToZero"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToZero")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "0"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "-[1-9][0-9]*")));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "[1-9][0-9]*")));
    }

    [Fact]
    public async Task Bools() {
      var source = @"
module SimpleTest {
  static method checkIfTrue(b: bool) returns (ret: bool) {
    if (b) {
        return true;
    }
    return false;
  }
}
".TrimStart();
      var program = Utils.Parse(Setup.GetDafnyOptions(output), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(2, methods.Count);
      Assert.True(methods.All(m => m.MethodName == "SimpleTest.checkIfTrue"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.checkIfTrue")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "false"));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "true"));
    }

    [Fact]
    public async Task Reals() {
      var source = @"
module SimpleTest {
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
      var program = Utils.Parse(Setup.GetDafnyOptions(output), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(7, methods.Count);
      Assert.True(
        methods.All(m => m.MethodName == "SimpleTest.compareToZero"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToZero")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "0.0"));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "1.0"));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "-1.0"));
      Assert.True(methods.Exists(m => Regex.IsMatch(m.ArgValues[0],
        "-[1-9][0-9]*\\.[0-9]*/[1-9][0-9]*\\.[0-9]*")));
      Assert.True(methods.Exists(m => Regex.IsMatch(m.ArgValues[0],
        "[1-9][0-9]*\\.[0-9]*/[1-9][0-9]*\\.[0-9]*")));
    }

    [Fact]
    public async Task BitVectors() {
      var source = @"
module SimpleTest {
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
      var program = Utils.Parse(DafnyOptions.Create(output), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(3, methods.Count);
      Assert.True(
        methods.All(m => m.MethodName == "SimpleTest.compareToBase"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToBase")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "(10 as bv10)"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\\([0-9] as bv10\\)")));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\\([1-9][0-9]+ as bv10\\)")));
    }

    [Fact]
    public async Task Chars() {
      var source = @"
module SimpleTest {
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
      var program = Utils.Parse(Setup.GetDafnyOptions(output), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(3, methods.Count);
      Assert.True(methods.All(m => m.MethodName == "SimpleTest.compareToB"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToB")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "'B'"));
      Assert.True(methods.Exists(m =>
        m.ArgValues[0].Length == 3 && m.ArgValues[0][1] > 'B'));
      Assert.True(methods.Exists(m =>
        m.ArgValues[0].Length == 3 && m.ArgValues[0][1] < 'B'));
    }

    [Fact]
    public async Task CharsUnspecified() {
      // This test case is different from the one above because the model would
      // not specify the exact value of c when the only constraint on it is that
      // c != 'B"
      var source = @"
module SimpleTest {
  static method compareToB(c: char) returns (b:bool) {
    if (c == 'B') {
      return false;
    } else {
      return true;
    }
  }
}
".TrimStart();
      var program = Utils.Parse(Setup.GetDafnyOptions(output), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(2, methods.Count);
      Assert.True(methods.All(m => m.MethodName == "SimpleTest.compareToB"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToB")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "'B'"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "'[^B]'")));
    }

  }
}
