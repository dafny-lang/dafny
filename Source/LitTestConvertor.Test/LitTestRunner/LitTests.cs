using Microsoft.Dafny;
using Xunit;
using XUnitExtensions;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace LitTestConvertor.Test.LitTestRunner {
  public class LitTests {
    [FileTheory]
    [LitTestData(Extension = ".dfy", InvokeCliDirectly = false)]
    [LitSubstitution("%baredafny", MainClass = typeof(Microsoft.Dafny.DafnyDriver))]
    [LitSubstitution("%dafny", MainClass = typeof(Microsoft.Dafny.DafnyDriver), Arguments = new [] { 
        "/countVerificationErrors:0",

        // We do not want absolute or relative paths in error messages, just the basename of the file
        "/useBaseNameForFileName:yes",

        // We do not want output such as "Compiled program written to Foo.cs"
        // from the compilers, since that changes with the target language
        "/compileVerbose:0",

        // Hide Boogie execution traces since they are meaningless for Dafny programs
        "/errorTrace:0"})]
    [LitSubstitution("%server", MainClass = typeof(Server))]
    [LitSubstitution("%diff", CLIPath = "diff")]
    public void LitTest(string path, LitTestConfiguration configuration) {
      LitTestCase.Run(path, configuration);
    }
  }
}