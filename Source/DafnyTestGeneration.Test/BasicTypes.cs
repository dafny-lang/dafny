// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore.Test;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test {
  public class BasicTypes : Setup {
    private readonly TextWriter output;

    public BasicTypes(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Ints(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {
  method {:testEntry} compareToZero(i: int) returns (ret: int) {
    if (i == 0) {
        return 0;
    } else if (i > 0) {
        return 1;
    }
    return -1;
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(3 <= methods.Count);
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

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Bools(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {
  method {:testEntry} checkIfTrue(b: bool) returns (ret: bool) {
    if (b) {
        return true;
    }
    return false;
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(2 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "SimpleTest.checkIfTrue"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.checkIfTrue")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "false"));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "true"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Reals(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {
  method {:testEntry} compareToZero(r: real) returns (ret: int) {
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
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(7 <= methods.Count);
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

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task BitVectors(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {
  method {:testEntry} compareToBase(r: bv10) returns (ret: int) {
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
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(3 <= methods.Count);
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

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Chars(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {
  method {:testEntry} compareToB(c: char) returns (ret: int) {
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
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(3 <= methods.Count);
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

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task CharsUnspecified(List<Action<DafnyOptions>> optionSettings) {
      // This test case is different from the one above because the model would
      // not specify the exact value of c when the only constraint on it is that
      // c != 'B"
      var source = @"
module SimpleTest {
  method {:testEntry} compareToB(c: char) returns (b:bool) {
    if (c == 'B') {
      return false;
    } else {
      return true;
    }
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(2 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "SimpleTest.compareToB"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.compareToB")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "'B'"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "'[^B]+'")));
    }

  }
}
