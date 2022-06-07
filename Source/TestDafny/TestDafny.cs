using CommandLine;
using Microsoft.Dafny;
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
    var dafnyArgs = new List<string>(testDafnyOptions.OtherArgs);
    dafnyArgs.Add($"/compile:0");
    
    
    string expectFile = testDafnyOptions.TestFile + ".expect";
    
    foreach(var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers()) {
        dafnyArgs = new List<string>(testDafnyOptions.OtherArgs);
        dafnyArgs.Add($"/noVerify");
        dafnyArgs.Add($"/compile:4");
        dafnyArgs.Add($"/compileTarget:{compiler.TargetId}");
        
        Console.Out.WriteLine(string.Join(" ", dafnyArgs));
        // TODO: Run test, compare to sourcefile.expect
      }  
    }
    
    return 0;
  }
}