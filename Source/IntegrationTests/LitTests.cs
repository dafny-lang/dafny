using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices;
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.IntegrationTest;
using TestDafny;
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
    private static readonly Assembly TestDafnyAssembly = typeof(TestDafny.MultiBackendTest).Assembly;
    private static readonly Assembly DafnyServerAssembly = typeof(Server).Assembly;

    private static readonly string RepositoryRoot = Path.GetFullPath("../../../../../"); // Up from Source/IntegrationTests/bin/Debug/net6.0/
    private static readonly string[] DefaultBoogieArguments = new[] {
      "/infer:j",
      "/proverOpt:O:auto_config=false",
      "/proverOpt:O:type_check=true",
      "/proverOpt:O:smt.case_split=3",
      "/proverOpt:O:smt.qi.eager_threshold=100",
      "/proverOpt:O:smt.delay_units=true",
      "/proverOpt:O:smt.arith.solver=2",
      "/proverOpt:PROVER_PATH:" + RepositoryRoot + $"../unzippedRelease/dafny/z3/bin/z3-{DafnyOptions.DefaultZ3Version}"
    };

    private static readonly LitTestConfiguration Config;

    static LitTests() {
      // Allow extra arguments to Dafny subprocesses. This can be especially
      // useful for capturing prover logs.
      var extraDafnyArguments =
        Environment.GetEnvironmentVariable("DAFNY_EXTRA_TEST_ARGUMENTS");

      IEnumerable<string> AddExtraArgs(IEnumerable<string> args, IEnumerable<string> local) {
        return (extraDafnyArguments is null ? args : args.Append(extraDafnyArguments)).Concat(local);
      }

      string[] defaultResolveArgs = new[] { "resolve", "--use-basename-for-filename" };
      string[] defaultVerifyArgs = new[] { "verify", "--use-basename-for-filename", "--cores:2", "--verification-time-limit:300" };
      //string[] defaultTranslateArgs = new[] { "translate", "--use-basename-for-filename", "--cores:2", "--verification-time-limit:300" };
      string[] defaultBuildArgs = new[] { "build", "--use-basename-for-filename", "--cores:2", "--verification-time-limit:300" };
      string[] defaultRunArgs = new[] { "run", "--use-basename-for-filename", "--cores:2", "--verification-time-limit:300" };

      var substitutions = new Dictionary<string, object> {
        { "%diff", "diff" },
        { "%trargs", "--use-basename-for-filename --cores:2 --verification-time-limit:300" },
        { "%binaryDir", "." },
        { "%z3", Path.Join("z3", "bin", $"z3-{DafnyOptions.DefaultZ3Version}") },
        { "%repositoryRoot", RepositoryRoot.Replace(@"\", "/") },
      };

      var commands = new Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> {
        {
          "%baredafny", (args, config) =>
            DafnyCommand(args, config, InvokeMainMethodsDirectly)
        }, {
          "%resolve", (args, config) =>
            DafnyCommand(AddExtraArgs(defaultResolveArgs, args), config, InvokeMainMethodsDirectly)
        }, {
          "%translate", (args, config) =>
            DafnyCommand(AddExtraArgs(new[]{"translate"}, args), config, InvokeMainMethodsDirectly)
        }, {
          "%verify", (args, config) =>
            DafnyCommand(AddExtraArgs(defaultVerifyArgs, args), config, InvokeMainMethodsDirectly)
        }, {
          "%build", (args, config) =>
            DafnyCommand(AddExtraArgs(defaultBuildArgs, args), config, InvokeMainMethodsDirectly)
        }, {
          "%run", (args, config) =>
            DafnyCommand(AddExtraArgs(defaultRunArgs, args), config, InvokeMainMethodsDirectly)
        }, {
          "%dafny", (args, config) =>
            DafnyCommand(AddExtraArgs(DafnyDriver.DefaultArgumentsForTesting, args), config, InvokeMainMethodsDirectly)
        }, {
          "%testDafnyForEachCompiler", (args, config) =>
            MainMethodLitCommand.Parse(TestDafnyAssembly, new []{ "for-each-compiler" }.Concat(args), config, InvokeMainMethodsDirectly)
        }, {
          "%server", (args, config) => // TODO
          {
            var shellArguments = new[] { DafnyServerAssembly.Location }.Concat(args);
            return new ShellLitCommand("dotnet", shellArguments, config.PassthroughEnvironmentVariables);
          }
        }, {
          "%boogie", (args, config) => // TODO
            new DotnetToolCommand("boogie",
              args.Concat(DefaultBoogieArguments),
              config.PassthroughEnvironmentVariables)
        }, {
          "%diff", (args, config) => DiffCommand.Parse(args.ToArray())
        }, {
          "%sed", (args, config) => SedCommand.Parse(args.ToArray())
        }, {
          "%OutputCheck", OutputCheckCommand.Parse
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
            new[] { "for-each-compiler", "--dafny", dafnyCliPath }.Concat(args), config, false);
        commands["%server"] = (args, config) =>
          new ShellLitCommand(Path.Join(dafnyReleaseDir, "DafnyServer"), args, config.PassthroughEnvironmentVariables);
        commands["%boogie"] = (args, config) =>
          new DotnetToolCommand("boogie",
            args.Concat(DefaultBoogieArguments),
            config.PassthroughEnvironmentVariables);
        substitutions["%z3"] = Path.Join(dafnyReleaseDir, "z3", "bin", $"z3-{DafnyOptions.DefaultZ3Version}");
      }

      Config = new LitTestConfiguration(substitutions, commands, features, DafnyDriver.ReferencedEnvironmentVariables);
    }

    public static ILitCommand DafnyCommand(IEnumerable<string> arguments, LitTestConfiguration config, bool invokeDirectly) {
      return invokeDirectly
        ? new DafnyDriverLitCommand(arguments, config)
        : new ShellLitCommand("dotnet", new[] { DafnyDriverAssembly.Location }.Concat(arguments), config.PassthroughEnvironmentVariables);
    }

    private readonly ITestOutputHelper output;

    public LitTests(ITestOutputHelper output) {
      this.output = output;
    }

    [FileTheory]
    [FileData(Includes = new[] { "**/*.dfy", "**/*.transcript" },
              Excludes = new[] { "**/Inputs/**/*", "**/Output/**/*"
              })]
    public void LitTest(string path) {
      LitTestCase.Run(path, Config, output);
    }
  }

  class DafnyDriverLitCommand : ILitCommand {
    private readonly string[] arguments;

    public DafnyDriverLitCommand(IEnumerable<string> arguments, LitTestConfiguration config) {
      this.arguments = arguments.ToArray();
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter,
      TextWriter errorWriter) {
      var exitCode = DafnyDriver.MainWithWriter(outputWriter, errorWriter, inputReader, arguments);
      return (exitCode, "", "");
    }

    public override string ToString() {
      return $"dafny {string.Join(" ", arguments)}";
    }
  }

  class MultiBackendLitCommand : ILitCommand {
    private readonly string[] arguments;

    public MultiBackendLitCommand(IEnumerable<string> arguments, LitTestConfiguration config) {
      this.arguments = arguments.ToArray();
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter,
      TextWriter errorWriter) {
      var exitCode = new MultiBackendTest(inputReader, outputWriter, errorWriter).Start(arguments.Prepend("for-each-compiler"));
      return (exitCode, "", "");
    }
  }
}

