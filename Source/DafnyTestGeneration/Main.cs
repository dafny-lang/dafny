using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration {

  public static class Main {

    /// <summary>
    /// Generate test methods for a certain Dafny program.
    /// </summary>
    /// <returns></returns>
    public static IEnumerable<TestMethod> GetTestMethodsForProgram(
      Program program, DafnyInfo? dafnyInfo = null) {

      // Translate the Program to Boogie:
      var oldPrintInstrumented = DafnyOptions.O.PrintInstrumented;
      DafnyOptions.O.PrintInstrumented = true;
      var boogiePrograms = Translator
        .Translate(program, program.reporter)
        .ToList().ConvertAll(tuple => tuple.Item2);
      DafnyOptions.O.PrintInstrumented = oldPrintInstrumented;

      // Create modifications of the program with assertions for each block\path
      ProgramModifier programModifier =
        DafnyOptions.O.TestGenOptions.Mode == TestGenerationOptions.Modes.Block
          ? new BlockBasedModifier()
          : new PathBasedModifier();
      dafnyInfo ??= new DafnyInfo(program);
      var modifications = programModifier.Modify(boogiePrograms);

      // Generate tests based on counterexamples produced from modifications
      var testMethods = new ConcurrentBag<TestMethod>();
      for (var i = modifications.Count - 1; i >= 0; i--) {
        var log = modifications[i].GetCounterExampleLog();
        if (log == null) {
          continue;
        }
        var testMethod = new TestMethod(dafnyInfo, log);
        if (testMethods.Contains(testMethod)) {
          continue;
        }
        testMethods.Add(testMethod);
        yield return testMethod;
      }
    }

    /// <summary>
    /// Return a Dafny class (as a string) with tests for the given Dafny file
    /// </summary>
    public static string GetTestClassForProgram(string sourceFile) {

      var result = "";
      var source = new StreamReader(sourceFile).ReadToEnd();
      var program = Utils.Parse(source, sourceFile);
      if (program == null) {
        return result;
      }
      var dafnyInfo = new DafnyInfo(program);
      var rawName = sourceFile.Split("/").Last().Split(".").First();

      result += $"include \"{rawName}.dfy\"\n";
      result += $"module {rawName}UnitTests {{\n";
      result += string.Join("\n", dafnyInfo.ToImport
        .Select(module => $"import {module}")) + "\n";

      result = GetTestMethodsForProgram(program, dafnyInfo)
        .Aggregate(result, (current, method) => current + method + "\n");

      return result + "}";
    }
  }
}