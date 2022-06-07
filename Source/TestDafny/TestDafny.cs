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

    // TODO: First just verify
    var dafnyArgs = new List<string>();
    dafnyArgs.Add("%baredafny");
    dafnyArgs.Add(testDafnyOptions.TestFile!);
    dafnyArgs = new List<string>(testDafnyOptions.OtherArgs);
    dafnyArgs.Add($"/compile:0");
    var (exitCode, output, error) = RunLitCommand(dafnyArgs);
    if (exitCode != 0) {
      throw new Exception("Verification failed");
    }
    
    string expectFile = testDafnyOptions.TestFile + ".expect";
    var expectedOutput = File.ReadAllText(expectFile);
    
    foreach(var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers()) {
        dafnyArgs = new List<string>();
        dafnyArgs.Add(testDafnyOptions.TestFile!);
        dafnyArgs.AddRange(testDafnyOptions.OtherArgs);
        dafnyArgs.Add($"/noVerify");
        dafnyArgs.Add($"/compile:4");
        dafnyArgs.Add($"/compileTarget:{compiler.TargetId}");
        
        (exitCode, output, error) = RunLitCommand(dafnyArgs);
        if (exitCode != 0) {
          throw new Exception("Execution failed");
        }
        
        AssertWithDiff.Equal(expectedOutput, output);
      }  
    }
    
    return 0;
  }

  private static (int, string, string) RunLitCommand(IEnumerable<string> arguments) {
    var line = string.Join(" ", arguments);
    var command = ILitCommand.Parse(line, null);
    return command.Execute(null, null, null, null);
  }
}