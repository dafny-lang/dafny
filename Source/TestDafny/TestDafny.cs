using System.Reflection;
using CommandLine;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using XUnitExtensions;
using XUnitExtensions.Lit;
using Parser = CommandLine.Parser;

public class TestDafnyOptions {

  [Value(0)]
  public string? TestFile { get; set; } = null;

  [Option("exit-code")]
  public int? ExpectedExitCode { get; set; } = 0;
  
  [Value(1)]
  public IEnumerable<string> OtherArgs { get; set; }
}

public class TestDafny {

  private static readonly Assembly DafnyDriverAssembly = typeof(DafnyDriver).Assembly;
    
  public static int Main(string[] args) {
    TestDafnyOptions? options = null;
    var parser = new Parser(with => with.EnableDashDash = true);
    parser.ParseArguments<TestDafnyOptions>(args).WithParsed(o => {
      options = o;
    });
    return RunTest(options!);
  }

  private static int RunTest(TestDafnyOptions testDafnyOptions) {
    var dafnyOptions = new DafnyOptions();
    var success = dafnyOptions.Parse(testDafnyOptions.OtherArgs.ToArray());
    if (!success) {
      // The same thing DafnyDriver does on options parsing errors
      return (int)DafnyDriver.ExitValue.PREPROCESSING_ERROR;
    }

    // First verify the file (and assume that verification should be successful).
    // Older versions of test files that now use %testdafny were sensitive to the number
    // of verification conditions (i.e. the X in "Dafny program verifier finished with X verified, 0 errors"),
    // but this was never meaningful and only added maintenance burden.
    // Here we only ensure that the exit code is 0, and as a sanity check ensures
    // that X is strictly more than 0.
    
    var dafnyArgs = new List<string>(testDafnyOptions.OtherArgs);
    dafnyArgs.Add($"/compile:0");
    dafnyArgs.Add(testDafnyOptions.TestFile!);
    dafnyArgs.AddRange(testDafnyOptions.OtherArgs);

    Console.Out.WriteLine("Verifying...");

    var (exitCode, output, error) = RunDafny(dafnyArgs);
    if (exitCode != 0) {
      Console.Out.WriteLine("Verification failed. Output:");
      Console.Out.WriteLine(output);
      Console.Out.WriteLine("Error:");
      Console.Out.WriteLine(error);
      return exitCode;
    }
    
    // Then execute the program for each available compiler.
    // Here we can pass /noVerify to save time since we already verified the program. 
    
    string expectFile = testDafnyOptions.TestFile + ".expect";
    var expectedOutput = "\nDafny program verifier did not attempt verification\n" +
      File.ReadAllText(expectFile);
    
    foreach(var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers()) {
        var result = RunWithCompiler(testDafnyOptions, compiler, expectedOutput);
        if (result != 0) {
          return result;
        }
      }
    }
    
    Console.Out.WriteLine($"All executions were successful and matched the expected output!");
    return 0;
  }

  private static int RunWithCompiler(TestDafnyOptions testDafnyOptions, Compiler compiler, string expectedOutput) {
    Console.Out.WriteLine($"Executing on {compiler.TargetLanguage}...");
    var dafnyArgs = new List<string> { testDafnyOptions.TestFile! };
    dafnyArgs.AddRange(testDafnyOptions.OtherArgs);
    dafnyArgs.Add("/noVerify");
    // /noVerify is interpreted pessimistically as "did not get verification success",
    // so we have to force compiling and running despite this.
    dafnyArgs.Add("/compile:4");
    dafnyArgs.Add($"/compileTarget:{compiler.TargetId}");
        
    var (exitCode, output, error) = RunDafny(dafnyArgs);
    if (exitCode == 0) {
      var diffMessage = AssertWithDiff.GetDiffMessage(expectedOutput, output);
      if (diffMessage == null) {
        return 0;
      }

      Console.Out.WriteLine(diffMessage);
      return 1;
    }
        
    // If we hit errors, check for known unsupported features for this compilation target
    if (OnlyUnsupportedFeaturesErrors(compiler, output)) {
      return 0;
    }

    Console.Out.WriteLine("Execution failed, for reasons other than known unsupported features. Output:");
    Console.Out.WriteLine(output);
    Console.Out.WriteLine("Error:");
    Console.Out.WriteLine(error);
    return exitCode;
  }
  
  private static (int, string, string) RunDafny(IEnumerable<string> arguments) {
    var dotnetArguments = new[] { DafnyDriverAssembly.Location }
      .Concat(arguments)
      .Concat(DafnyDriver.DefaultArgumentsForTesting);
    var command = new ShellLitCommand("dotnet", dotnetArguments, DafnyDriver.ReferencedEnvironmentVariables);
    return command.Execute(null, null, null, null);
  }

  private static bool OnlyUnsupportedFeaturesErrors(Compiler compiler, string output) {
    using (StringReader sr = new StringReader(output)) {
      string? line;
      while ((line = sr.ReadLine()) != null) {
        if (!IsAllowedOutputLine(compiler, line)) {
          return false;
        }
      }
    }

    return true;
  }

  private static bool IsAllowedOutputLine(Compiler compiler, string line) {
    line = line.Trim();
    if (line.Length == 0) {
      return true;
    }
    // This is the first non-blank line we expect when we pass /noVerify
    if (line == "Dafny program verifier did not attempt verification") {
      return true;
    }
    
    // This is output if the compiler emits any errors
    if (line.StartsWith("Wrote textual form of partial target program to")) {
      return true;
    }
    
    var prefixIndex = line.IndexOf(UnsupportedFeatureException.MessagePrefix, StringComparison.Ordinal);
    if (prefixIndex < 0) {
      return false;
    }

    var featureDescription = line[(prefixIndex + UnsupportedFeatureException.MessagePrefix.Length)..];
    var feature = FeatureDescriptionAttribute.ForDescription(featureDescription);
    if (compiler.UnsupportedFeatures.Contains(feature)) {
      return true;
    }
    
    // This is an internal inconsistency error
    throw new Exception($"Compiler rejected feature '{feature}', which is not an element of its UnsupportedFeatures set");
  }
}