using System.Linq;
using System.Runtime.InteropServices;

namespace Microsoft.Dafny;

public static class DafnyCliTests {

  // Environment variables that the CLI directly or indirectly (through target language tools) reads.
  // This is defined for the benefit of testing infrastructure to ensure that they are maintained
  // through separate processes.
  public static readonly string[] ReferencedEnvironmentVariables = [
    "PATH",
    "HOME",
    "DOTNET_NOLOGO",
    "DAFNY_INTEGRATION_TESTS_IN_PROCESS",
    "DAFNY_INTEGRATION_TESTS_MODE",
    "DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS",
    "DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE",
    "DAFNY_INTEGRATION_TESTS_ROOT_DIR"
  ];

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

  public static readonly string[] DefaultArgumentsForTesting = [
    // Try to verify 2 verification conditions at once
    "/vcsCores:2",

    // We do not want absolute or relative paths in error messages, just the basename of the file
    "/useBaseNameForFileName",

    // We do not want output such as "Compiled program written to Foo.cs"
    // from the compilers, since that changes with the target language
    "/compileVerbose:0",

    // Set a default resource limit, to catch cases where verification runs off the rails
    "/rlimit:50000000",

    // Also include a time limit, because we do care about using too much time.
    "/timeLimit:300",
    "/allowAxioms:1",

    // test results do not include source code snippets
    "/showSnippets:0"
  ];

  public static readonly string[] NewDefaultArgumentsForTesting = [
    // Use the new resolver
    "--type-system-refresh",
    "--general-traits=datatype",
    "--general-newtypes",

    // Try to verify 2 verification conditions at once
    "--cores=2",

    // We do not want absolute or relative paths in error messages, just the basename of the file
    "--use-basename-for-filename",

    // Set a default resource limit, to catch cases where verification runs off the rails
    "--resource-limit:50e6",

    "--allow-axioms",
    // Also include a time limit, because we do care about using too much time.
    "--verification-time-limit:300",

    // test results do not include source code snippets
    "--show-snippets:false"
  ];
}
