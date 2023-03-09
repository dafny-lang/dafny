using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test {

  public class Various {


    [Fact]
    public async Task NoInlining() {
      var source = @"
module M {
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
}
".TrimStart();
      var program = Utils.Parse(Setup.GetDafnyOptions(), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(3, methods.Count);
      Assert.Equal(2, methods.Count(m => m.MethodName == "M.Inlining.b"));
      Assert.Equal(1, methods.Count(m => m.MethodName == "M.Inlining.a"));
      Assert.True(methods.All(m => !m.DafnyInfo.IsStatic("M.Inlining.b")));
      Assert.True(methods.All(m => !m.DafnyInfo.IsStatic("M.Inlining.a")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m => m.ValueCreation.Count == 1));
      Assert.True(methods.Exists(m => m.ArgValues[1] == "0"));
      Assert.True(methods.Count(m => m.ArgValues[1] != "0") is 1 or 2);
      Assert.True(methods.All(m =>
        Regex.IsMatch(m.ArgValues[1], "-?[0-9]+")));
    }

    [Fact]
    public async Task Inlining() {
      var source = @"
module M {
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
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TargetMethod = "M.Inlining.a";
      options.TestGenOptions.TestInlineDepth = 2;
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(2, methods.Count);
      Assert.True(methods.All(m => m.MethodName == "M.Inlining.a"));
      Assert.True(methods.All(m => !m.DafnyInfo.IsStatic("M.Inlining.a")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m => m.ValueCreation.Count == 1));
      Assert.True(methods.Exists(m => m.ArgValues[1] == "0"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ArgValues[1], "-?[1-9][0-9]*")));
    }

    [Fact]
    public async Task PathBasedTests() {
      var source = @"
module Paths {
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
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.Mode =
        TestGenerationOptions.Modes.Path;
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(8, methods.Count);
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

    [Fact]
    public async Task BlockBasedTests() {
      var source = @"
module Paths {
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
      var program = Utils.Parse(Setup.GetDafnyOptions(), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
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

    [Fact]
    public async Task RecursivelyExtractObjectFields() {
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
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TargetMethod =
        "Objects.List.IsACircleOfLessThanThree";
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.True(methods.Count >= 2);
      Assert.True(methods.All(m =>
        m.MethodName == "Objects.List.IsACircleOfLessThanThree"));
      Assert.True(methods.All(m =>
        m.DafnyInfo.IsStatic("Objects.List.IsACircleOfLessThanThree")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      // This test is too specific. A test input may be valid and still not satisfy it.
      /*
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count == 1 && m.Assignments[0] == ("v0", "next", "v0") &&
        m.ValueCreation.Count == 1) ||
        (m.Assignments.Count == 2 && m.Assignments[1] == ("v0", "next", "v1") &&
        m.Assignments[0] == ("v1", "next", "v0") &&
        m.ValueCreation.Count == 2)));
        */
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count > 2 && m.ValueCreation.Count > 2 &&
        m.Assignments.Last() == ("v0", "next", "v1") &&
        m.Assignments[^2] == ("v1", "next", "v2")) ||
        (m.Assignments.Count == 2 && m.ValueCreation.Count == 2 &&
        m.Assignments[1] == ("v0", "next", "v1") &&
        m.Assignments[0] == ("v1", "next", "v1"))));
      Assert.True(methods.Exists(m =>
        (m.Assignments.Count == 1 &&
        m.Assignments[0] == ("v0", "next", "null") &&
        m.ValueCreation.Count == 1) ||
        (m.Assignments.Count == 2 && m.Assignments[1] == ("v0", "next", "v1") &&
        m.Assignments[0] == ("v1", "next", "null") &&
        m.ValueCreation.Count == 2)));
    }

    [Fact]
    public async Task RecursivelyExtractDatatypeFields() {
      var source = @"
module DataTypes {
  datatype Node = Cons(next:Node) | Nil
  class List {
    static method Depth(node: Node) returns (i:int) {
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
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TargetMethod =
        "DataTypes.List.Depth";
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(3, methods.Count);
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

    [Fact]
    public async Task NonNullableObjects() {
      var source = @"
module Module {
  class Value<T> {
    var v:T;
    constructor(v:T) {
      this.v := v;
    }
  }
  method ignoreNonNullableObject(v:Value<char>, b:bool) {
    assert b;
  }
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TargetMethod =
        "Module.ignoreNonNullableObject";
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(1, methods.Count);
      var m = methods[0];
      Assert.Equal("Module.ignoreNonNullableObject", m.MethodName);
      Assert.True(m.DafnyInfo.IsStatic("Module.ignoreNonNullableObject"));
      Assert.Equal(2, m.ArgValues.Count);
      Assert.Equal(1, m.ValueCreation.Count);
      Assert.Equal("Module.Value<char>", m.ValueCreation[0].type.ToString());
    }

    [Fact]
    public async Task DeadCode() {
      var source = @"
module M {
  method m(a:int) returns (b:int)
    requires a > 0
  {
    if (a == 0) {
      return 0;
    }
    return 1;
  }
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.WarnDeadCode = true;
      var stats = await Main.GetDeadCodeStatistics(program).ToListAsync();
      Assert.True(stats.Contains("Code at (6,14) is potentially unreachable."));
      Assert.Equal(2, stats.Count); // second is line with stats
    }

    [Fact]
    public async Task NoDeadCode() {
      var source = @"
method m(a:int) returns (b:int)
{
  if (a == 0) {
    return 0;
  }
  return 1;
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.WarnDeadCode = true;
      var stats = await Main.GetDeadCodeStatistics(program).ToListAsync();
      Assert.Equal(1, stats.Count); // the only line with stats
    }

    [Fact]
    public async Task TypePolymorphism() {
      var source = @"
module Test {
  method IsEvenLength<K>(s: seq<K>) returns (isEven: bool)
  {
    if (|s| % 2 == 0) {
      return true;
    } else {
      return false;
    }
  }
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TargetMethod = "Test.IsEvenLength";
      options.TestGenOptions.SeqLengthLimit = 1;
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(2, methods.Count);
      Assert.True(methods.All(m => m.MethodName == "Test.IsEvenLength"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Test.IsEvenLength")));
      Assert.True(methods.All(m => m.ArgValues.Count == 1));
      Assert.True(methods.All(m => m.ValueCreation.Count == 1));
      Assert.True(methods.All(m => m.NOfTypeArgs == 1));
      Assert.True(methods.Exists(m => m.ValueCreation[0].value == "[]"));
      Assert.True(methods.Exists(m =>
        Regex.IsMatch(m.ValueCreation[0].value, "\\[[0-9]+\\]")));
    }

    [Fact]
    public async Task FunctionMethod() {
      var source = @"
module Math {
  function Max(a:int, b:int):int {
    if (a > b) then a else b
  }
  function Min(a:int, b:int):int {
    -Max(-a, -b)
  }
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TestInlineDepth = 2;
      options.TestGenOptions.TargetMethod = "Math.Min";
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.True(2 <= methods.Count);
      Assert.True(methods.All(m => m.MethodName == "Math.Min"));
      Assert.True(methods.All(m => m.DafnyInfo.IsStatic("Math.Min")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m => m.ValueCreation.Count == 0));
      Assert.True(methods.All(m => m.NOfTypeArgs == 0));
      Assert.True(methods.Exists(m => int.Parse(m.ArgValues[0]) < int.Parse(m.ArgValues[1])));
      Assert.True(methods.Exists(m => int.Parse(m.ArgValues[1]) <= int.Parse(m.ArgValues[0])));
    }

    [Fact]
    public async Task FunctionMethodShortCircuit() {
      var source = @"
module ShortCircuit {
  function Or(a:bool):bool {
    a || OnlyFalse(a)
  }
  function OnlyFalse(a:bool):bool
    requires !a
  {
    false
  }
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      options.TestGenOptions.TestInlineDepth = 1;
      options.TestGenOptions.TargetMethod = "ShortCircuit.Or";
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(2, methods.Count);
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
    [Fact]
    public async Task MultipleModules() {
      var source = @"
module A {
  function m(i:int):int requires i == 0 { i }
}
module B {
  function m(c:char):char requires c == '0' { c }
}
module C {
  function m(r:real):real requires r == 0.0 { r }
}
".TrimStart();
      var options = Setup.GetDafnyOptions();
      var program = Utils.Parse(options, source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
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

    [Fact]
    public async Task Oracles() {
      var source = @"
module M {
  class Instance {  
    var i:int;
    method setI(i:int) 
      requires i == 10
      ensures this.i == i 
      modifies this
    { 
      this.i := i;
    }    
  }  
}
".TrimStart();
      var program = Utils.Parse(Setup.GetDafnyOptions(), source);
      var methods = await Main.GetTestMethodsForProgram(program).ToListAsync();
      Assert.Equal(1, methods.Count);
      Assert.True(methods.All(m =>
        m.MethodName == "M.Instance.setI"));
      Assert.True(methods.All(m =>
        !m.DafnyInfo.IsStatic("M.Instance.setI")));
      Assert.True(methods.All(m => m.ArgValues.Count == 2));
      Assert.True(methods.All(m => m.ToString().Contains("expect v0.i == 10")));
    }

  }
}
