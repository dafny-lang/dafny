// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Test;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;

namespace DafnyTestGeneration.Test {

  public class Collections : Setup {
    private readonly TextWriter output;

    public Collections(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Tuples(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module SimpleTest {
  method {:testEntry} tuple(tseq: seq<(int, (bool, char))>) returns (i:int) {
    if (|tseq| == 0) {
        return 0;
    } else if (|tseq| > 0 && tseq[0].0 == 5) {
        return 1;
    } else if (|tseq| > 0 && tseq[0].1.1 == 'R') {
        return 2;
    }
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = Utils.Parse(new BatchErrorReporter(options), source, false);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.True(3 <= methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName == "SimpleTest.tuple"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("SimpleTest.tuple")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.Exists(m =>
        m.ValueCreation.Count == 1 &&
        m.ValueCreation.First().type.ToString() == "seq<(int, (bool, char))>"));
      Assert.True(methods.Count(m =>
        m.ValueCreation.Count == 3 &&
        m.ValueCreation.Exists(vc => vc.type.ToString() == "(bool, char)") &&
        m.ValueCreation.Exists(vc => vc.type.ToString() == "(int, (bool, char))") &&
        m.ValueCreation.Exists(vc => vc.type.ToString() == "seq<(int, (bool, char))>")) >= 2);
      Assert.True(methods.Exists(m =>
        m.ValueCreation.Count == 3 &&
        m.ValueCreation.Exists(vc => vc.value.ToString().StartsWith("(5,"))));
      Assert.True(methods.Exists(m =>
        m.ValueCreation.Count == 3 &&
        m.ValueCreation.Exists(vc => vc.value.ToString().Contains("\'R\')"))));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    private async Task StringLength(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module C {
  method {:testEntry} compareStringLengthToOne(s: string) returns (ret: int) {
      if (|s| == 1) {
          return 0;
      }
      if (|s| > 1) {
          return 1;
      }
      if (|s| == 0) {
          return -1;
      }
  }
}

".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = Utils.Parse(new BatchErrorReporter(options), source, false);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.True(3 <= methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName == "C.compareStringLengthToOne"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("C.compareStringLengthToOne")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "\"\""));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\".\"")));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "\"..+\"")));
    }

  }
}
