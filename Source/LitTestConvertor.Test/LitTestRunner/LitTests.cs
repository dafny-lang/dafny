using System;
using System.Collections.Generic;
using System.Reflection;
using Microsoft.Dafny;
using Xunit;
using XUnitExtensions;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace LitTestConvertor.Test.LitTestRunner {
  public class LitTests {
    
    private static readonly LitTestConfiguration CONFIG = new () {
      MainMethodSubstitutions = new Dictionary<string, (Assembly, string[])> {
        { "%baredafny", (typeof(Microsoft.Dafny.DafnyDriver).Assembly, Array.Empty<string>()) },
        { "%dafny", (typeof(Microsoft.Dafny.DafnyDriver).Assembly, new [] { 
          "/countVerificationErrors:0",

          // We do not want absolute or relative paths in error messages, just the basename of the file
          "/useBaseNameForFileName:yes",

          // We do not want output such as "Compiled program written to Foo.cs"
          // from the compilers, since that changes with the target language
          "/compileVerbose:0",

          // Hide Boogie execution traces since they are meaningless for Dafny programs
          "/errorTrace:0"
        })},
        { "%server", (typeof(Server).Assembly, Array.Empty<string>()) }
      },
      
      InvokeMainMethodsDirectly = Environment.GetEnvironmentVariable("XUNIT_INVOKE_MAIN_METHODS_DIRECTLY") == "true",
      
      Substitions = new Dictionary<string, string> {
        { "%diff", "diff" }
      },
    };
    
    [FileTheory]
    [LitTestData(Extension = ".dfy")]
    public void LitTest(string path) {
      LitTestCase.Run(path, CONFIG);
    }
  }
}