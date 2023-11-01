using System.Linq;
using System.Runtime.InteropServices;

namespace Microsoft.Dafny;

public static class DafnyCliTests {

  // Environment variables that the CLI directly or indirectly (through target language tools) reads.
  // This is defined for the benefit of testing infrastructure to ensure that they are maintained
  // through separate processes.
  public static readonly string[] ReferencedEnvironmentVariables = { "PATH", "HOME", "DOTNET_NOLOGO" };

  static DafnyCliTests() {
    if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
      ReferencedEnvironmentVariables = ReferencedEnvironmentVariables
        .Concat(new[] { // Careful: Keep this list in sync with the one in lit.site.cfg
          "APPDATA",
          "HOMEDRIVE",
          "HOMEPATH",
          "INCLUDE",
          "LIB",
          "LOCALAPPDATA",
          "NODE_PATH",
          "ProgramFiles",
          "ProgramFiles(x86)",
          "SystemRoot",
          "SystemDrive",
          "TEMP",
          "TMP",
          "USERPROFILE"
        }).ToArray();
    }
  }

  public static readonly string[] DefaultArgumentsForTesting = new[] {
    // Try to verify 2 verification conditions at once
    "/vcsCores:2",

    // We do not want absolute or relative paths in error messages, just the basename of the file
    "/useBaseNameForFileName",

    // We do not want output such as "Compiled program written to Foo.cs"
    // from the compilers, since that changes with the target language
    "/compileVerbose:0",
      
    // Set a default time limit, to catch cases where verification time runs off the rails
    "/timeLimit:300",

    // test results do not include source code snippets
    "/showSnippets:0"
  };

  public static readonly string[] NewDefaultArgumentsForTesting = new[] {
    // Try to verify 2 verification conditions at once
    "--cores=2",

    // We do not want absolute or relative paths in error messages, just the basename of the file
    "--use-basename-for-filename",

    // Set a default time limit, to catch cases where verification time runs off the rails
    "--verification-time-limit=300",

    // test results do not include source code snippets
    "--show-snippets:false"
  };
}