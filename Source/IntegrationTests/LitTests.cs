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

    // Change this to true in order to debug the execution of commands like %dafny.
    // This is false by default because the main dafny CLI implementation currently has shared static state, which
    // causes errors when invoking the CLI in the same process on multiple inputs in sequence, much less in parallel.
    private const bool InvokeMainMethodsDirectly = false;

    private static readonly Assembly DafnyDriverAssembly = typeof(Dafny.Dafny).Assembly;
    private static readonly Assembly TestDafnyAssembly = typeof(TestDafny.TestDafny).Assembly;
    private static readonly Assembly DafnyServerAssembly = typeof(Server).Assembly;

    private static readonly LitTestConfiguration Config;

    static LitTests() {
      // Allow extra arguments to Dafny subprocesses. This can be especially
      // useful for capturing prover logs.
      var extraDafnyArguments =
        Environment.GetEnvironmentVariable("DAFNY_EXTRA_TEST_ARGUMENTS");

      IEnumerable<string> AddExtraArgs(IEnumerable<string> args, IEnumerable<string> local) {
        return (extraDafnyArguments is null ? args : args.Append(extraDafnyArguments)).Concat(local);
      }

      var repositoryRoot = Path.GetFullPath("../../../../../"); // Up from Source/IntegrationTests/bin/Debug/net6.0/

      var substitutions = new Dictionary<string, object> {
        { "%diff", "diff" },
        { "%verifyargs", "--use-basename-for-filename --cores:2 --verification-time-limit:300" },
        { "%resolveargs", "--use-basename-for-filename" },
        { "%binaryDir", "." },
        { "%z3", Path.Join("z3", "bin", "z3") },
        { "%repositoryRoot", repositoryRoot.Replace(@"\", "/") },
      };

      var commands = new Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> {
        {
          "%baredafny", (args, config) =>
            MainMethodLitCommand.Parse(DafnyDriverAssembly, args, config, InvokeMainMethodsDirectly)
        }, {
          "%dafny", (args, config) =>
            MainMethodLitCommand.Parse(DafnyDriverAssembly, AddExtraArgs(DafnyDriver.DefaultArgumentsForTesting, args),
              config, InvokeMainMethodsDirectly)
        }, {
          "%testDafnyForEachCompiler", (args, config) =>
            MainMethodLitCommand.Parse(TestDafnyAssembly, new []{ "for-each-compiler" }.Concat(args), config,
              InvokeMainMethodsDirectly)
        }, {
          "%server", (args, config) =>
            MainMethodLitCommand.Parse(DafnyServerAssembly, args, config, InvokeMainMethodsDirectly)
        }, {
          "%diff", (args, config) => DiffCommand.Parse(args.ToArray())
        }, {
          "%sed", (args, config) => SedCommand.Parse(args.ToArray())
        }, {
          "%OutputCheck", (args, config) =>
            OutputCheckCommand.Parse(args, config)
        }
      };

      // Silence dotnet's welcome message
      Environment.SetEnvironmentVariable("DOTNET_NOLOGO", "true");

      string[] features;
      if (RuntimeInformation.IsOSPlatform(OSPlatform.Linux)) {
        features = new[] { "ubuntu", "posix" };
      } else if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        features = new[] { "windows" };
        string path = System.Reflection.Assembly.GetExecutingAssembly().Location;
        var directory = System.IO.Path.GetDirectoryName(path);
        Environment.SetEnvironmentVariable("DOTNET_CLI_HOME", directory);
        if (directory != null) {
          Directory.SetCurrentDirectory(directory);
        }

        Environment.SetEnvironmentVariable("HOME",
          Environment.GetEnvironmentVariable("HOMEDRIVE") + Environment.GetEnvironmentVariable("HOMEPATH"));
      } else if (RuntimeInformation.IsOSPlatform(OSPlatform.OSX)) {
        features = new[] { "macosx", "posix" };
      } else {
        throw new Exception($"Unsupported OS: {RuntimeInformation.OSDescription}");
      }

      substitutions["%args"] = DafnyDriver.NewDefaultArgumentsForTesting;

      var dafnyReleaseDir = Environment.GetEnvironmentVariable("DAFNY_RELEASE");
      if (dafnyReleaseDir != null) {
        var dafnyCliPath = Path.Join(dafnyReleaseDir, "dafny");
        commands["%baredafny"] = (args, config) =>
          new ShellLitCommand(dafnyCliPath, args, config.PassthroughEnvironmentVariables);
        commands["%dafny"] = (args, config) =>
          new ShellLitCommand(dafnyCliPath,
            AddExtraArgs(DafnyDriver.DefaultArgumentsForTesting, args), config.PassthroughEnvironmentVariables);
        commands["%testDafnyForEachCompiler"] = (args, config) =>
          MainMethodLitCommand.Parse(TestDafnyAssembly,
            new[] { "for-each-compiler", "--dafny", dafnyCliPath }.Concat(args), config,
            InvokeMainMethodsDirectly);
        commands["%server"] = (args, config) =>
          new ShellLitCommand(Path.Join(dafnyReleaseDir, "DafnyServer"), args, config.PassthroughEnvironmentVariables);
        substitutions["%z3"] = Path.Join(dafnyReleaseDir, "z3", "bin", "z3");
      }

      Config = new LitTestConfiguration(substitutions, commands, features, DafnyDriver.ReferencedEnvironmentVariables);
    }

    private readonly ITestOutputHelper output;

    public LitTests(ITestOutputHelper output) {
      this.output = output;
    }

    [FileTheory]
    [FileData(Includes = new[] { "**/*.dfy", "**/*.transcript" },
              Excludes = new[] { "**/Inputs/**/*", "**/Output/**/*",
                "**/libraries/**",
                "examples/induction-principle-code/*"
              })]
    public void LitTest(string path) {
      LitTestCase.Run(path, Config, output);
    }
  }
}
