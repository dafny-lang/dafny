// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class WarningTests : Setup {

  private static readonly Regex Errors = new("returned ([0-9]+) error");
  private static readonly Regex Warnings = new Regex("returned ([0-9]+) warning");

  private static int Count(Regex toCount, string output) {
    var match = toCount.Match(output);
    if (match.Success && int.TryParse(match.Groups[1].Value, out var count)) {
      return count;
    }
    return 0;
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task NoTestEntryPoint(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
  method m (i:int) { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NoTestEntryError, outputString);
    Assert.Equal(1, Count(Errors, outputString));
    Assert.Equal(0, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task NoExternalModule(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
method {:testEntry} m (i:int) { }
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NoExternalModuleError, outputString);
    Assert.Equal(1, Count(Errors, outputString));
    Assert.Equal(0, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task InlinedMethodNotReachable(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module A {
import opened B
method {:testEntry} a () { }
}
module B {
method {:testInline 1} b() {}
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.InlinedMethodNotReachableWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task InlinedMethodReachable(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module A {
import opened B
method {:testEntry} a () {b(); }
}
module B {
method {:testInline 1} b() {}
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(0, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task MalformedAttribute(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module A {
import opened B
method {:testEntry} a () {b(); }
}
module B {
method {:testInline -1} b() {}
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.MalformedAttributeError, outputString);
    Assert.Equal(1, Count(Errors, outputString));
    Assert.Equal(0, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task UnsupportedInputTypeTrait(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
trait T {}
method {:testEntry} m (t:T) { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.UnsupportedInputTypeError, outputString);
    Assert.Equal(1, Count(Errors, outputString));
    Assert.Equal(0, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task UnsupportedInputTypeClass(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
class C {}
method {:testEntry} m (c:C) { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NotFullySupportedInputTypeWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task UnsupportedInputTypeRecursive(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
class C {}
datatype D = A(c:C) | D(d:D)
method {:testEntry} m (d:D) { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NotFullySupportedInputTypeWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task UnsupportedInputTypeRecursive2(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
class C {}
method {:testEntry} m (s:seq<C>) { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NotFullySupportedInputTypeWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task UnsupportedRecieverType(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
  class C {
    method {:testEntry} m () { } // this should raise a warning
  }
  datatype D = D {
    predicate {:testEntry} p () { true } // this should not raise any warnings
  }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NotFullySupportedInputTypeWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task SmallTimeLimit(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
method {:testEntry} {:timeLimit 100} m () { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.SmallTimeLimitWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task NoWitness(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
module M {
type why = i:int | i == 9 || i == 3
method {:testEntry} m (w:why) { }
}
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains(FirstPass.NoWitnessWarning, outputString);
    Assert.Equal(0, Count(Errors, outputString));
    Assert.Equal(1, Count(Warnings, outputString));
  }

  [Theory]
  [MemberData(nameof(OptionSettings))]
  public async Task MalformedInput(List<Action<DafnyOptions>> optionSettings) {
    var source = new StringReader(@"
This is an unparsable program
".TrimStart());
    var output = new StringBuilder();
    var options = GetDafnyOptions(optionSettings, new StringWriter(output));
    await Main.GetTestClassForProgram(source, null, options).ToListAsync();
    var outputString = output.ToString();
    Assert.Contains("Error", outputString);
  }

}