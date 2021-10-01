using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.Dafny;
using Xunit;
using XUnitExtensions;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace IntegrationTests.LitTestRunner {
  public class LitTests {

    private static readonly Assembly dafnyDriverAssembly = typeof(DafnyDriver).Assembly;
    private static readonly Assembly dafnyServerAssembly = typeof(Server).Assembly;

    private static readonly string[] defaultDafnyArguments = new[] {
      "/countVerificationErrors:0",

      // We do not want absolute or relative paths in error messages, just the basename of the file
      "/useBaseNameForFileName",

      // We do not want output such as "Compiled program written to Foo.cs"
      // from the compilers, since that changes with the target language
      "/compileVerbose:0",

      // Hide Boogie execution traces since they are meaningless for Dafny programs
      "/errorTrace:0"
    };
    
    private static ILitCommand MainWithArguments(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      
      return MainMethodLitCommand.Parse(assembly, arguments, config, invokeDirectly);
    }

    private static readonly LitTestConfiguration CONFIG = new () {
      Commands = new Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> {
        { "%baredafny", (args, config) => 
          MainWithArguments(dafnyDriverAssembly, args, config, false) },
        { "%dafny", (args, config) => 
          MainWithArguments(dafnyDriverAssembly, defaultDafnyArguments.Concat(args), config, true) },
        { "%server", (args, config) => 
          MainWithArguments(dafnyServerAssembly, args, config, false) },
      },
      
      // TODO: speed this up by using AssertWithDiff
      Substitions = new Dictionary<string, string> {
        { "%diff", "diff" }
      },
      
      PassthroughEnvironmentVariables = new []{ "PATH", "HOME" },
    };
    
    [FileTheory]
    [LitTestData(Extension = ".dfy")]
    public void LitTest(string path) {
      LitTestCase.Run(path, CONFIG);
    }
  }
}