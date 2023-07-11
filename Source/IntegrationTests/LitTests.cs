using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using Microsoft.Dafny;
using TestDafny;
using Xunit;
using Xunit.Abstractions;
using XUnitExtensions;
using XUnitExtensions.Lit;

[assembly: TestCollectionOrderer("XUnitExtensions.TestCollectionShardFilter", "XUnitExtensions")]

namespace IntegrationTests {

  public class LitTests {

    private static readonly bool InvokeMainMethodsDirectly;

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
      // Set this to true in order to debug the execution of commands like %dafny.
      // This is false by default because the main dafny CLI implementation currently has shared static state, which
      // causes errors when invoking the CLI in the same process on multiple inputs in sequence, much less in parallel.
      InvokeMainMethodsDirectly = Environment.GetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_IN_PROCESS") == "true";

      // Allow extra arguments to Dafny subprocesses. This can be especially
      // useful for capturing prover logs.
      var extraDafnyArguments =
        Environment.GetEnvironmentVariable("DAFNY_EXTRA_TEST_ARGUMENTS");

      IEnumerable<string> AddExtraArgs(IEnumerable<string> args, IEnumerable<string> local) {
        return (extraDafnyArguments is null ? args : args.Append(extraDafnyArguments)).Concat(local);
      }

      string[] defaultResolveArgs = new[] { "resolve", "--use-basename-for-filename", "--show-snippets:false" };
      string[] defaultVerifyArgs = new[] { "verify", "--use-basename-for-filename", "--show-snippets:false", "--cores:2", "--verification-time-limit:300" };
      //string[] defaultTranslateArgs = new[] { "translate", "--use-basename-for-filename", "--cores:2", "--verification-time-limit:300" };
      string[] defaultBuildArgs = new[] { "build", "--use-basename-for-filename", "--show-snippets:false", "--cores:2", "--verification-time-limit:300" };
      string[] defaultRunArgs = new[] { "run", "--use-basename-for-filename", "--show-snippets:false", "--cores:2", "--verification-time-limit:300" };

      var substitutions = new Dictionary<string, object> {
        { "%diff", "diff" },
        { "%trargs", "--use-basename-for-filename --show-snippets:false --cores:2 --verification-time-limit:300" },
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
            DafnyCommand(AddExtraArgs(new[] { "translate" }, args), config, InvokeMainMethodsDirectly)
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
            MainMethodLitCommand.Parse(TestDafnyAssembly, new[] { "for-each-compiler" }.Concat(args), config,
              InvokeMainMethodsDirectly)
        }, {
          "%server", (args, config) =>
            MainMethodLitCommand.Parse(DafnyServerAssembly, args, config, InvokeMainMethodsDirectly)
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
        : new ShellLitCommand("dotnet", new[] { DafnyDriverAssembly.Location }.Concat(arguments),
          config.PassthroughEnvironmentVariables);
    }

    private readonly ITestOutputHelper output;

    public LitTests(ITestOutputHelper output) {
      this.output = output;
    }

    [FileTheory]
    [FileData(Includes = new[] { "**/*.dfy", "**/*.transcript" },
              Excludes = new[] { "**/Inputs/**/*", "**/Output/**/*", "libraries/**/*"
              })]
    public void LitTest(string path) {
      var testPath = path.Replace("TestFiles/LitTests/LitTest", "");
      var mode = Environment.GetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_MODE");
      switch (mode) {
        case "uniformity-convert":
          // Need to convert the original source path,
          // not the copy in the output directory of this project.
          var sourcePath = Path.Join(Environment.GetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_ROOT_DIR"), testPath);
          ConvertToMultiBackendTestIfNecessary(sourcePath);
          return;
        case "uniformity-check":
          var testCase = LitTestCase.Read(path, Config);
          if (NeedsConverting(testCase)) {
            Assert.Fail($"Non-uniform test case that exercises backends: {testPath}\nConvert to using %testDafnyForEachCompiler or add a '// NONUNIFORM: <reason>' command");
          }
          break;
        case null or "":
          LitTestCase.Run(path, Config, output);
          break;
        default:
          throw new ArgumentException(
            $"Unrecognized value of DAFNY_INTEGRATION_TESTS_MODE environment variable: {mode}");
      }
    }

    private static bool NeedsConverting(LitTestCase testCase) {
      var allOtherFileExtensions = DafnyOptions.Default.Plugins.SelectMany(plugin => plugin.GetCompilers(DafnyOptions.Default))
        .SelectMany(compiler => compiler.SupportedExtensions).ToHashSet();
      allOtherFileExtensions.Remove(".dfy");

      foreach (var command in testCase.Commands) {
        var leafCommand = GetLeafCommand(command);

        if (leafCommand is NonUniformTestCommand) {
          return false;
        }

        if (leafCommand is ShellLitCommand or DafnyDriverLitCommand) {
          var arguments = GetDafnyArguments(leafCommand);
          if (arguments != null) {
            if (arguments.Any(arg => allOtherFileExtensions.Any(arg.EndsWith))) {
              return false;
            }

            if (arguments.Any(arg => arg is "/compile:3" or "/compile:4" or "run" or "translate")) {
              return true;
            }
          }
        }
      }

      return false;
    }

    private static void ConvertToMultiBackendTestIfNecessary(string path) {
      var testCase = LitTestCase.Read(path, Config);

      if (!NeedsConverting(testCase)) {
        return;
      }

      bool IgnoreArgument(string arg, string testFilePath) {
        if (arg == testFilePath) {
          return true;
        }

        if (DafnyDriver.NewDefaultArgumentsForTesting.Contains(arg)) {
          return true;
        }
        if (DafnyDriver.DefaultArgumentsForTesting.Contains(arg)) {
          return true;
        }

        if (arg is "%dafny" or "%basedafny" or "%args" or "verify" or "run" or "--no-verify" or "/noVerify") {
          return true;
        }

        if (arg.StartsWith("/compile:") || arg.StartsWith("/compileTarget:")) {
          return true;
        }
        if (arg.StartsWith("--target") || arg.StartsWith("-t:") || arg.StartsWith("-t=")) {
          return true;
        }
        // MultiBackendTest always adds all three of these to temporary files.
        if (arg.StartsWith("/print:") || arg.StartsWith("/dprint:") || arg.StartsWith("/rprint:")) {
          return true;
        }
        if (arg.StartsWith("/env")) {
          return true;
        }

        return false;
      }

      // Analyze the commands to figure out any extra options to %testDafnyForEachCompiler
      var commonExtraOptions = new HashSet<string>();
      var extraOptionsLocked = false;
      string? expectFile = null;
      // null is used here to mean /compile:0 or dafny verify
      var backends = new List<string?>();
      var wasLegacyCli = false;
      foreach (var command in testCase.Commands) {
        var leafCommand = GetLeafCommand(command);
        switch (leafCommand) {
          case ShellLitCommand or DafnyDriverLitCommand: {
              var arguments = GetDafnyArguments(leafCommand);
              if (arguments == null) {
                throw new ArgumentException();
              }

              if (arguments.Any(arg => arg.StartsWith("/compile"))) {
                wasLegacyCli = true;
              }

              var backend = GetBackendFromCommand(arguments);
              if (backends.Contains(backend)) {
                throw new ArgumentException($"More than one command for the same backend: {backend}");
              }
              backends.Add(backend);

              // Filter out options we can ignore
              var options = arguments.Where(arg => !IgnoreArgument(arg, testCase.FilePath));
              if (extraOptionsLocked) {
                foreach (string arg in options) {
                  if (!commonExtraOptions.Contains(arg)) {
                    throw new ArgumentException($"Inconsistent option: {arg}");
                  }
                }
              } else {
                foreach (var arg in options) {
                  commonExtraOptions.Add(arg);
                }
                if (backend != null) {
                  extraOptionsLocked = true;
                }
              }

              break;
            }
          case DiffCommand diffCommand:
            // The last line should be the standard '// RUN: %diff "%s.expect" "%t"' line
            expectFile = diffCommand.ExpectedPath;
            break;
          default:
            throw new ArgumentException($"Unrecognized command type: {command}");
        }
      }

      if (expectFile == null) {
        throw new ArgumentException($"No %diff command found");
      }
      var expectContent = File.ReadAllText(expectFile);

      // Partition according to the "\nDafny program verifier did not attempt verification/finished with..." lines.
      // Each call to dafny creates such a line, so splitting on them results in one more chunk than calls.
      var delimiter = new Regex("\nDafny program verifier[^\n]*\n");
      var chunks = delimiter.Split(expectContent).ToList();
      if (chunks.Count != backends.Count + 1) {
        throw new ArgumentException();
      }

      // Whether we called dafny normally for each backend,
      // or whether we first just verified,
      // the first chunk will include any warnings that we will want to check
      // in our own first verify-only call
      // and remove from the other output chunks.
      string verifierChunk = chunks.First();
      if (!string.IsNullOrWhiteSpace(verifierChunk)) {
        var verifierExpectPath = $"{path}.verifier.expect";

        // Need to adjust the line numbers of any warnings or errors
        // since we're replacing many individual RUN lines with one :P
        var adjustedVerifierChunk = AdjustLineNumbers(verifierChunk, 1 - testCase.Commands.Count());

        File.WriteAllText(verifierExpectPath, adjustedVerifierChunk);
      }

      if (backends.First() == null) {
        backends.RemoveAt(0);
        chunks.RemoveAt(0);
      }
      // Now the first chunk is the verifier output before the execution output,
      // so skip it.
      chunks.RemoveAt(0);

      string? commonExpectChunk = null;
      var exceptions = false;
      foreach (var (backend, chunk) in backends.Zip(chunks)) {
        if (backend != null) {
          var expectedChunk = string.IsNullOrWhiteSpace(verifierChunk) ? chunk : chunk.Replace(verifierChunk, "");
          if (commonExpectChunk == null) {
            commonExpectChunk = expectedChunk;
          } else if (commonExpectChunk != expectedChunk) {
            var exceptionPath = $"{path}.{backend}.expect";
            File.WriteAllText(exceptionPath, expectedChunk);
            exceptions = true;
          }
        }
      }
      File.WriteAllText(expectFile, commonExpectChunk);

      var testFileLines = File.ReadAllLines(testCase.FilePath);

      var multiBackendCommand = "// RUN: %testDafnyForEachCompiler \"%s\"";
      var testDafnyExtraArgs = new SortedSet<string>();
      foreach (var extraOption in commonExtraOptions) {
        // Map some common legacy options to new CLI options
        testDafnyExtraArgs.Add(extraOption switch {
          "/unicodeChar:0" => "--unicode-char:false",
          "/unicodeChar:1" => "--unicode-char:true",
          "/functionSyntax:3" => "--function-syntax:3",
          "/functionSyntax:4" => "--function-syntax:4",
          "/spillTargetCode:2" => "--spill-translation",
          "/spillTargetCode:3" => "--spill-translation",
          "/optimizeErasableDatatypeWrapper:0" => "--optimize-erasable-datatype-wrapper:false",
          "/verifyAllModules" => "--verify-included-files",
          "/errorLimit:0" => "--error-limit:0",
          "/deprecation:0" => "--warn-deprecation:false",
          _ => extraOption
        });
      }
      if (wasLegacyCli) {
        // Accounting for different defaults
        testDafnyExtraArgs.Add("--relax-definite-assignment");
      }
      if (testDafnyExtraArgs.Any()) {
        multiBackendCommand += " -- " + string.Join(" ", testDafnyExtraArgs);
      }

      var newLines = new List<string> {
        multiBackendCommand,
      };
      newLines.AddRange(testFileLines.Where(line => ILitCommand.Parse(line, Config) == null));
      if (exceptions) {
        // Intentionally leaving the reason off to force a manual review
        // to specify the right reason (likely a GitHub issue),
        // since the command will fail to parse without a reason.
        newLines.Insert(0, "// NONUNIFORM:");
      }

      File.WriteAllLines(testCase.FilePath, newLines);
    }

    private static string AdjustLineNumbers(string messages, int delta) {
      var lines = MultiBackendTest.ReadAllLines(messages);
      var pattern = new Regex("\\((\\d*),");
      var adjusted = lines.Select(line =>
        pattern.Replace(line, match =>
          $"({int.Parse(match.Groups[1].Value) + delta},"
        ) + Environment.NewLine
      );
      return string.Join("", adjusted);
    }

    private static ILitCommand GetLeafCommand(ILitCommand command) {
      if (command is LitCommandWithRedirection lcwr) {
        return GetLeafCommand(lcwr.Command);
      }

      if (command is DelayedLitCommand dlc) {
        return GetLeafCommand(dlc.Factory());
      }

      return command;
    }

    private static IList<string>? GetDafnyArguments(ILitCommand command) {
      switch (command) {
        case ShellLitCommand slc:
          if (slc.Arguments.Length >= 1 && slc.Arguments[0].EndsWith("Dafny.dll")) {
            return slc.Arguments[1..];
          } else {
            return null;
          }
        case DafnyDriverLitCommand ddlc:
          return ddlc.Arguments;
        default:
          return null;
      }
    }

    private static string? GetBackendFromCommand(IEnumerable<string> arguments) {
      if (arguments.Any(arg => arg is "/compile:0" or "verify")) {
        return null;
      }

      var patterns = new[] {
        new Regex("--target[:=]([^\\s]*)"),
        new Regex("-t[:=]([^\\s]*)"),
        new Regex("/compileTarget:([^\\s]*)"),
      };
      foreach (var pattern in patterns) {
        var match = arguments.Select(arg => pattern.Match(arg)).SingleOrDefault(m => m.Success);
        if (match != null) {
          return match.Groups[1].Value;
        }
      }

      return "cs";
    }
  }

  class DafnyDriverLitCommand : ILitCommand {
    public string[] Arguments { get; }

    public DafnyDriverLitCommand(IEnumerable<string> arguments, LitTestConfiguration config) {
      this.Arguments = arguments.ToArray();
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter,
      TextWriter errorWriter) {
      var exitCode = DafnyDriver.MainWithWriters(outputWriter, errorWriter, inputReader, Arguments);
      return (exitCode, "", "");
    }

    public override string ToString() {
      return $"dafny {string.Join(" ", Arguments)}";
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