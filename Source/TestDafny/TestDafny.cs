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
      return -1;
    }

    var dafnyArgs = new List<string>(testDafnyOptions.OtherArgs);
    dafnyArgs.Add($"/compile:0");
    dafnyArgs.Add(testDafnyOptions.TestFile!);

    Console.Out.WriteLine("Verifying...");

    var (exitCode, output, error) = RunDafny(dafnyArgs);
    if (exitCode != 0) {
      throw new Exception("Verification failed");
    }
    
    string expectFile = testDafnyOptions.TestFile + ".expect";
    var expectedOutput = "\nDafny program verifier did not attempt verification\n" +
      File.ReadAllText(expectFile);
    
    foreach(var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers()) {
        Console.Out.WriteLine($"Executing on {compiler.TargetLanguage}...");
        dafnyArgs = new List<string> { testDafnyOptions.TestFile! };
        dafnyArgs.AddRange(testDafnyOptions.OtherArgs);
        dafnyArgs.Add("/noVerify");
        dafnyArgs.Add("/useBaseNameForFileName");
        dafnyArgs.Add("/compileVerbose:0");
        dafnyArgs.Add("/compile:4");
        dafnyArgs.Add($"/compileTarget:{compiler.TargetId}");
        
        (exitCode, output, error) = RunDafny(dafnyArgs);
        if (exitCode != 0) {
          // Check for known unsupported features for this compilation target
          if (OnlyUnsupportedFeaturesErrors(compiler, output)) {
            // Carry on, nothing more to see here...
            continue;
          }
          
          throw new Exception("Execution failed");
        }
        
        AssertWithDiff.Equal(expectedOutput, output);
      }  
    }
    
    return 0;
  }

  private static (int, string, string) RunDafny(IEnumerable<string> arguments) {
    var dotnetArguments = new[] { DafnyDriverAssembly.Location }.Concat(arguments);
    // TODO: Refactor list of passthrough environment variables somewhere this
    // and IntegrationTests can both reference
    var command = new ShellLitCommand("dotnet", dotnetArguments, new[] { "PATH", "HOME", "DOTNET_NOLOGO" });
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
    if (line == "Dafny program verifier did not attempt verification") {
      return true;
    }
    
    var prefixIndex = line.IndexOf(FeatureNotSupportedException.MessagePrefix, StringComparison.Ordinal);
    if (prefixIndex < 0) {
      return false;
    }

    var featureDescription = line[(prefixIndex + FeatureNotSupportedException.MessagePrefix.Length)..];
    var feature = FeatureDescriptionAttribute.ForDescription(featureDescription);
    return compiler.UnsupportedFeatures.Contains(feature);
  }
}