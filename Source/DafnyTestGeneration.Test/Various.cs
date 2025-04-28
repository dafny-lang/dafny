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

  public class Various : Setup {
    private readonly TextWriter output;

    public Various(ITestOutputHelper output) {
      this.output = new WriterFromOutputHelper(output);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task NoInlining(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  method {:testEntry} b (i:int) returns (r:int) {
    if (i == 0) {
        return 7;
    } else {
        return 81;
    }
  }
  method {:testEntry} a (i:int) returns (r:int) {
    r := b(i);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(3 <= methods.Count);
      Assert.True(2 <= methods.Count(m => m.MethodName == "M.b"));
      Assert.Equal(1, methods.Count(m => m.MethodName == "M.a"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("M.b")));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("M.a")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "0"));
      Assert.True(methods.Count(m => m.ArgValues[0] != "0") is 1 or 2);
      Assert.True(methods.All(m =>
        Regex.IsMatch(m.ArgValues[0], "-?[0-9]+")));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Inlining(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  method {:testInline} b (i:int) returns (r:int) {
    if (i == 0) {
        return 7;
    } else {
        return 81;
    }
  }
  method {:testEntry} a (i:int) returns (r:int) {
    r := b(i);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count >= 2);
      Assert.True(methods.All(m => m.MethodName == "M.a"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("M.a")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "0"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[0], "-?[1-9][0-9]*")));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task NestedInlining(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  function {:testInline} min (a:int, b:int):int {
    if a < b then a else b
  }
  function {:testInline} max (a:int, b:int):int {
    min(b, a)
  }
  method {:testEntry} test (a:int, b:int) returns (r:int) {
    r := max(a, b);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count >= 2);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SelectiveInlining(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  function {:testInline} min (a:int, b:int):int {
    if a < b then a else b
  }
  function max (a:int, b:int):int {
    if a > b then a else b
  }
  method {:testEntry} test(a:int, b:int) returns (r:int) {
    r := max(a, b);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.Single(methods);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FunctionCallInAMethodTranslation(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  function {:testInline} max (a:int, b:int):int {
    if a > b then a else b
  }
  method {:testEntry} test(a:int, b:int) returns (r:int) {
    r := max(a, b);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(2 <= methods.Count);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task InliningRecursion(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  function {:testInline 2} mod3 (n:int):int 
    requires n >= 0
    decreases n
  {
    if n == 0 then 0 else
    if n == 1 then 1 else
    if n == 2 then 2 else
    mod3(n-3)
  }
  method {:testEntry} test(n:int) returns (r:int) 
    requires n >= 3
  {
    r := mod3(n);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count >= 3);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task InliningNoRecursion(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  function {:testInline} mod3 (n:int):int 
    requires n >= 0
    decreases n
  {
    if n == 0 then 0 else
    if n == 1 then 1 else
    if n == 2 then 2 else
    mod3(n-3)
  }
  method {:testEntry} test(n:int) returns (r:int) 
    requires n >= 3
  {
    r := mod3(n);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count < 3);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task PathBasedTests(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Paths {
  method {:testEntry} eightPaths (i:int)
    returns (divBy2:bool, divBy3:bool, divBy5:bool)
  {
    divBy2 := ifThenElse(i % 2 == 0, true, false);
    divBy3 := ifThenElse(i % 3 == 0, true, false);
    divBy5 := ifThenElse(i % 5 == 0, true, false);
  }
  predicate {:testInline} ifThenElse(condition:bool, thenBranch:bool, elseBranch:bool) {
    if condition then thenBranch else elseBranch
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      options.TestGenOptions.Mode =
        TestGenerationOptions.Modes.Path;
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(8 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "Paths.eightPaths"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Paths.eightPaths")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      var values = methods.Select(m =>
          int.TryParse(m.ArgValues[0], out var result) ? (int?)result : null)
        .ToList();
      Assert.True(values.All(i => i != null));
      Assert.True(values.Exists(i => i % 2 == 0 && i % 3 == 0 && i % 5 == 0));
      Assert.True(values.Exists(i => i % 2 == 0 && i % 3 == 0 && i % 5 != 0));
      Assert.True(values.Exists(i => i % 2 == 0 && i % 3 != 0 && i % 5 == 0));
      Assert.True(values.Exists(i => i % 2 == 0 && i % 3 != 0 && i % 5 != 0));
      Assert.True(values.Exists(i => i % 2 != 0 && i % 3 == 0 && i % 5 == 0));
      Assert.True(values.Exists(i => i % 2 != 0 && i % 3 == 0 && i % 5 != 0));
      Assert.True(values.Exists(i => i % 2 != 0 && i % 3 != 0 && i % 5 == 0));
      Assert.True(values.Exists(i => i % 2 != 0 && i % 3 != 0 && i % 5 != 0));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task BranchBasedTests(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Paths {
  method {:testEntry} eightPaths (i:int)
    returns (divBy2:bool, divBy3:bool, divBy5:bool)
  {
    divBy2 := ifThenElse(i % 2 == 0, true, false);
    divBy3 := ifThenElse(i % 3 == 0, true, false);
    divBy5 := ifThenElse(i % 5 == 0, true, false);
  }
  predicate {:testInline} ifThenElse(condition:bool, thenBranch:bool, elseBranch:bool) {
    if condition then thenBranch else elseBranch
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      options.TestGenOptions.Mode =
        TestGenerationOptions.Modes.InlinedBlock;
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count is >= 2 and <= 6);
      Assert.True(methods.All(m => m.MethodName == "Paths.eightPaths"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Paths.eightPaths")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      var values = methods.Select(m =>
          int.TryParse(m.ArgValues[0], out var result) ? (int?)result : null)
        .ToList();
      Assert.True(values.All(i => i != null));
      Assert.True(values.Exists(i => i % 2 == 0));
      Assert.True(values.Exists(i => i % 2 != 0));
      Assert.True(values.Exists(i => i % 3 == 0));
      Assert.True(values.Exists(i => i % 3 != 0));
      Assert.True(values.Exists(i => i % 5 == 0));
      Assert.True(values.Exists(i => i % 5 != 0));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task BlockBasedTests(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Paths {
  method {:testEntry} eightPaths (i:int)
    returns (divBy2:bool, divBy3:bool, divBy5:bool)
  {
    divBy2 := ifThenElse(i % 2 == 0, true, false);
    divBy3 := ifThenElse(i % 3 == 0, true, false);
    divBy5 := ifThenElse(i % 5 == 0, true, false);
  }
  predicate {:testInline} ifThenElse(condition:bool, thenBranch:bool, elseBranch:bool) {
    if condition then thenBranch else elseBranch
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count is >= 1 and <= 2);
      Assert.True(methods.All(m => m.MethodName == "Paths.eightPaths"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Paths.eightPaths")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      var values = methods.Select(m =>
          int.TryParse(m.ArgValues[0], out var result) ? (int?)result : null)
        .ToList();
      Assert.True(values.All(i => i != null));
      Assert.True(values.Exists(i => i % 2 == 0 || i % 3 == 0 || i % 5 == 0));
      Assert.True(values.Exists(i => i % 2 != 0 || i % 3 != 0 || i % 5 != 0));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task RecursivelyExtractObjectFields(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Objects {
  class Node {
      var next: Node?;
      constructor (next:Node?) {
          this.next := next;
      }
  }
  class List {
    static method {:testEntry} IsACircleOfTwoOrLessNodes(node: Node) returns (b: bool) {
        if node.next == null { 
          return false;
        } else if node.next == node { 
          return true;
        } else if node.next.next == null || node.next.next == node.next {
          return false;
        } else if node.next.next == node { 
          return true;
        }
        return false;
    }
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(methods.Count >= 5);
      Assert.True(methods.All(m =>
        m.MethodName == "Objects.List.IsACircleOfTwoOrLessNodes"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("Objects.List.IsACircleOfTwoOrLessNodes")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      // First return statement:
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count == 1 && m.ValueCreation.Count == 1 &&
         m.Assignments.Last() == ("node0", "next", "null"))));
      // Second return statement:
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count == 1 && m.ValueCreation.Count == 1 &&
         m.Assignments.Last() == ("node0", "next", "node0"))));
      // Third return statement:
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count == 2 && m.ValueCreation.Count == 2 &&
         m.Assignments.Last() == ("node0", "next", "node1") &&
         (m.Assignments[^2] == ("node1", "next", "null") ||
          m.Assignments[^2] == ("node1", "next", "node1")))));
      // Fourth return statements:
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count == 2 && m.ValueCreation.Count == 2 &&
         m.Assignments.Last() == ("node0", "next", "node1") &&
         m.Assignments[^2] == ("node1", "next", "node0"))));
      // Final return statements:
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count > 2 && m.ValueCreation.Count > 2 &&
         m.Assignments.Last() == ("node0", "next", "node1") &&
         m.Assignments[^2] == ("node1", "next", "node2"))));
    }

    /// <summary>
    /// This test addresses the situation in which there is a class-type object
    /// that does not matter for the construction of a counterexample.
    /// Furthermore, this class-type object is self-referential,
    /// with a field of the same type. Test generation must not enter infinite
    /// loop and must figure out that it needs to set the field of the object
    /// to itself.
    /// </summary>
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task TestByDefaultConstructionOfSelfReferentialValue(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {

    class LoopingList {

        var next:LoopingList;
        var value:int;

        constructor() {
            value := 0;
            next := this;
        }

        method {:testEntry} getValue() returns (value:int) {
            return this.value;
        }
    }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.Single(methods);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task RecursivelyExtractDatatypeFields(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module DataTypes {
  datatype Node = Cons(next:Node) | Nil
  class List {
    static method {:testEntry} Depth(node: Node) returns (i:int) {
      if (node.Nil?) {
        return 0;
      } else if (node.next.Nil?) {
        return 1;
      } else {
        return 2;
      }
    }
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(3 <= methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName == "DataTypes.List.Depth"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("DataTypes.List.Depth")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation[0].value == "DataTypes.Node.Nil"));
      Assert.True(methods.Exists(m =>
        m.ValueCreation.Count == 1));
      Assert.True(methods.Exists(m =>
        m.ValueCreation.Count == 2 &&
        m.ValueCreation[1].value == $"DataTypes.Node.Cons(next:={m.ValueCreation[0].id})"));
      Assert.True(methods.Exists(m =>
        m.ValueCreation.Count == 3 &&
        m.ValueCreation[1].value == $"DataTypes.Node.Cons(next:={m.ValueCreation[0].id})" &&
        m.ValueCreation[2].value == $"DataTypes.Node.Cons(next:={m.ValueCreation[1].id})"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task NonNullableObjects(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Module {
  class Value<T> {
    var v:T;
    constructor(v:T) {
      this.v := v;
    }
  }
  method {:testEntry} ignoreNonNullableObject(v:Value<char>, b:bool) returns (b2:bool) {
    return b;
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.Single(methods);
      var m = methods[0];
      Assert.Equal("Module.ignoreNonNullableObject", m.MethodName);
      Assert.True(m.DafnyInfo.IsStatic("Module.ignoreNonNullableObject"));
      Assert.Equal(2, m.ArgValues.Count);
      Assert.Single(m.ValueCreation);
      Assert.Equal("Module.Value<char>", m.ValueCreation[0].type.ToString());
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DeadCode(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  method {:testEntry} m(a:int) returns (b:int)
    requires a > 0
  {
    if (a == 0) {
      return 0;
    }
    return 1;
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      options.TestGenOptions.WarnDeadCode = true;
      var stats = await TestGenerator.GetDeadCodeStatistics(program, new Modifications(options)).ToListAsync();
      Assert.Contains(stats, s => s.Contains("(6,14) is potentially unreachable."));
      Assert.Equal(1, stats.Count(line => line.Contains("unreachable"))); // second is line with stats
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task CoverageReport(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  method {:testEntry} m(a:int) returns (b:bool)
    requires a > 0
  {                                             // fully covered (method's entry point)
    b := if IsPositive(a) then true else false; // partially covered because there are two branches
    if !IsPositive(a) {                         // fully covered
      b := false;                               // not covered
    }
  }                                             // fully covered (method's exit point)
  predicate {:testInline} IsPositive(n:int) {
    n > 0                                       // fully covered
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      options.TestGenOptions.WarnDeadCode = true;
      options.TestGenOptions.Mode = TestGenerationOptions.Modes.InlinedBlock;
      var coverageReport = new CoverageReport("", "", "", null);
      await TestGenerator.GetDeadCodeStatistics(new StringReader(source), null, options, coverageReport).ToListAsync();
      Assert.NotEmpty(coverageReport.AllFiles());
      var fileId = coverageReport.AllFiles().First();
      Assert.Equal(6, coverageReport.CoverageSpansForFile(fileId).Count());
      Assert.Equal(4, coverageReport.CoverageSpansForFile(fileId).Count(
        coverageSpan => coverageSpan.Label == CoverageLabel.FullyCovered));
      Assert.Equal(1, coverageReport.CoverageSpansForFile(fileId).Count(
        coverageSpan => coverageSpan.Label == CoverageLabel.PartiallyCovered));
      Assert.Equal(1, coverageReport.CoverageSpansForFile(fileId).Count(
        coverageSpan => coverageSpan.Label == CoverageLabel.NotCovered));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task NoDeadCode(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
method {:testEntry} m(a:int) returns (b:int)
{
  if (a == 0) {
    return 0;
  }
  return 1;
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      options.TestGenOptions.WarnDeadCode = true;
      var stats = await TestGenerator.GetDeadCodeStatistics(program, new Modifications(options)).ToListAsync();
      Assert.Single(stats); // the only line with stats
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task TypePolymorphism(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Test {
  method {:testEntry} IsEvenLength<K>(s: seq<K>) returns (isEven: bool)
  {
    if (|s| % 2 == 0) {
      return true;
    } else {
      return false;
    }
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      options.TestGenOptions.SeqLengthLimit = 1;
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(2 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "Test.IsEvenLength"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Test.IsEvenLength")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 1));
      Assert.True(methods.All(m => m.NOfTypeArgs == 1));
      Assert.True(methods.Exists(m => m.ValueCreation[0].value == "[]"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ValueCreation[0].value, "\\[[0-9]+\\]")));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task InlineGhostCode(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module Math {
  lemma {:testInline} Max(a:int, b:int) returns (i:int) {
    return if (a > b) then a else b;
  }
  lemma {:testEntry} Min(a:int, b:int) returns (i:int)  {
    return -Max(-a, -b);
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(2 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "Math.Min"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Math.Min")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.All(m => m.NOfTypeArgs == 0));
      Assert.True(methods.Exists(m => int.Parse(m.ArgValues[0]) < int.Parse(m.ArgValues[1])));
      Assert.True(methods.Exists(m => int.Parse(m.ArgValues[1]) >= int.Parse(m.ArgValues[0])));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FunctionMethodShortCircuit(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module ShortCircuit {
  function {:testEntry} Or(a:bool): bool {
    a || OnlyFalse(a)
  }
  function {:testInline} OnlyFalse(a:bool):bool
    requires !a
  {
    false
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.True(2 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "ShortCircuit.Or"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("ShortCircuit.Or")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.All(m => m.NOfTypeArgs == 0));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "true"));
      Assert.True(methods.Exists(m => m.ArgValues[0] == "false"));
    }

    /// <summary>
    /// If this fails, consider amending ProgramModifier.MergeBoogiePrograms
    /// </summary>
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MultipleModules(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module A {
  function {:testEntry} m(i:int):int requires i == 0 { i }
}
module B {
  function {:testEntry} m(c:char):char requires c == '0' { c }
}
module C {
  function {:testEntry} m(r:real):real requires r == 0.0 { r }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.Equal(3, methods.Count);
      Assert.True(methods.Exists(m => m.MethodName == "A.m" &&
                                        m.DafnyInfo.IsStatic("A.m") &&
                                        m.ValueCreation.Count == 0 &&
                                        m.Assignments.Count == 0 &&
                                        m.ArgValues.Count == 1 &&
                                        m.ArgValues[0] == "0"));
      Assert.True(methods.Exists(m => m.MethodName == "B.m" &&
                                        m.DafnyInfo.IsStatic("B.m") &&
                                        m.ValueCreation.Count == 0 &&
                                        m.Assignments.Count == 0 &&
                                        m.ArgValues.Count == 1 &&
                                        m.ArgValues[0] == "'0'"));
      Assert.True(methods.Exists(m => m.MethodName == "C.m" &&
                                        m.DafnyInfo.IsStatic("C.m") &&
                                        m.ValueCreation.Count == 0 &&
                                        m.Assignments.Count == 0 &&
                                        m.ArgValues.Count == 1 &&
                                        m.ArgValues[0] == "0.0"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task Oracles(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  class Instance {  
    var i:int;
    method {:testEntry} setI(i:int) 
      requires i == 10
      ensures this.i == i 
      modifies this
    { 
      this.i := i;
    }    
  }  
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.Single(methods);
      Assert.True(methods.All(m =>
        m.MethodName == "M.Instance.setI"));
      Assert.True(methods.All(m =>
        !m.DafnyInfo.IsStatic("M.Instance.setI")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m => m.ToString().Contains("expect instance0.i == 10")));
    }

    /// <summary>
    /// This test may fail if function to method translation implemented by AddByMethodRewriter
    /// does not use the cloner to copy the body of the function
    /// </summary>
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FunctionToMethodTranslation(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {

  function {:testEntry} test(b: bool): bool {
      assert true by {
        calc { true; }
      }
      true
  }
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      await GetTestMethodsForProgram(program);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MethodWithNoVerificationGoal(List<Action<DafnyOptions>> optionSettings) {
      var source = @"
module M {
  method {:testEntry} m(b: bool) {}
}
".TrimStart();
      var options = GetDafnyOptions(optionSettings, output);
      var program = await Parse(new BatchErrorReporter(options), source, false);
      var methods = await GetTestMethodsForProgram(program);
      Assert.Single(methods);
    }

  }
}
