using System.Reflection;
using CommandLine;
using Microsoft.Dafny;
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

    var dafnyArgs = new List<string>();
    dafnyArgs = new List<string>(testDafnyOptions.OtherArgs);
    dafnyArgs.Add($"/compile:0");
    dafnyArgs.Add(testDafnyOptions.TestFile!);

    var (exitCode, output, error) = RunDafny(dafnyArgs);
    if (exitCode != 0) {
      throw new Exception("Verification failed");
    }
    
    string expectFile = testDafnyOptions.TestFile + ".expect";
    var expectedOutput = "\nDafny program verifier did not attempt verification\n" +
      File.ReadAllText(expectFile);
    
    foreach(var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers()) {
        dafnyArgs = new List<string>();
        dafnyArgs.Add(testDafnyOptions.TestFile!);
        dafnyArgs.AddRange(testDafnyOptions.OtherArgs);
        dafnyArgs.Add("/noVerify");
        dafnyArgs.Add("/useBaseNameForFileName");
        dafnyArgs.Add("/compileVerbose:0");
        dafnyArgs.Add("/compile:4");
        dafnyArgs.Add($"/compileTarget:{compiler.TargetId}");
        
        (exitCode, output, error) = RunDafny(dafnyArgs);
        if (exitCode != 0) {
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
    return command!.Execute(null, null, null, null);
  }
}