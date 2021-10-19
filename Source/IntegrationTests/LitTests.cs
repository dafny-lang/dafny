using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices;
using Microsoft.Dafny;
using Xunit;
using Xunit.Abstractions;
using XUnitExtensions;
using XUnitExtensions.Lit;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace IntegrationTests {
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
      "/errorTrace:0",
      
      // Set a default time limit, to catch cases where verification time runs off the rails
      "/timeLimit:300"
    };

    private static ILitCommand MainWithArguments(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      return MainMethodLitCommand.Parse(assembly, arguments, config, invokeDirectly);
    }

    private static readonly LitTestConfiguration CONFIG = new() {
      Commands = new Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> {
        { "%baredafny", (args, config) =>
          MainWithArguments(dafnyDriverAssembly, args, config, false) },
        { "%dafny", (args, config) =>
          MainWithArguments(dafnyDriverAssembly, defaultDafnyArguments.Concat(args), config, false) },
        { "%server", (args, config) =>
          MainWithArguments(dafnyServerAssembly, args, config, false) },
      },

      Substitions = new Dictionary<string, string> {
        { "%diff", "diff" },
        { "%binaryDir", "." },
        { "%z3", Path.Join("z3", "bin", "z3") },
        { "%refmanexamples", Path.Join("TestFiles", "LitTests", "LitTest", "refman", "examples") }
      },

      PassthroughEnvironmentVariables = new[] { "PATH", "HOME" },
    };

    static LitTests() {
      var dafnyReleaseDir = Environment.GetEnvironmentVariable("DAFNY_RELEASE");
      if (dafnyReleaseDir != null) {
        CONFIG.Commands["%baredafny"] = (args, config) =>
          new ShellLitCommand(config, Path.Join(dafnyReleaseDir, "dafny"), args, config.PassthroughEnvironmentVariables);
        CONFIG.Commands["%dafny"] = (args, config) =>
          new ShellLitCommand(config, Path.Join(dafnyReleaseDir, "dafny"), defaultDafnyArguments.Concat(args), config.PassthroughEnvironmentVariables);
        CONFIG.Commands["%server"] = (args, config) =>
          new ShellLitCommand(config, Path.Join(dafnyReleaseDir, "DafnyServer"), args, config.PassthroughEnvironmentVariables);
        CONFIG.Substitions["%z3"] = Path.Join(dafnyReleaseDir, "z3", "bin", "z3");
      }

      if (RuntimeInformation.IsOSPlatform(OSPlatform.Linux)) {
        CONFIG.Features = new[] { "ubuntu", "posix" };
      } else if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        CONFIG.Features = new[] { "windows" };
      } else if (RuntimeInformation.IsOSPlatform(OSPlatform.OSX)) {
        CONFIG.Features = new[] { "macosx", "posix" };
      } else {
        throw new Exception($"Unsupported OS: {RuntimeInformation.OSDescription}");
      }
    }

    private readonly ITestOutputHelper output;

    public LitTests(ITestOutputHelper output) {
      this.output = output;
    }

    [FileTheory]
    [FileData(Includes = new [] { "**/*.dfy", "**/*.transcript" },
              Excludes = new [] { "**/Inputs/**/*" })]
    public void LitTest(string path) {
      LitTestCase.Run(path, CONFIG, output);
    }
  }
}