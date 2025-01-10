using System.CommandLine;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using CommandLine;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using XUnitExtensions;
using XUnitExtensions.Lit;

namespace TestDafny;

[Verb("for-each-compiler", HelpText = "Execute the given test file for every compiler, and assert the output matches the <test file>.expect file.")]
public class ForEachCompilerOptions {

  [Value(0, Required = true, MetaName = "Test file", HelpText = "The *.dfy file to test.")]
  public string? TestFile { get; set; } = null;

  [Option("dafny", HelpText = "The dafny CLI to test with. Defaults to the locally built DafnyDriver project.")]
  public string? DafnyCliPath { get; set; } = null;

  [Value(1, MetaName = "Dafny CLI arguments", HelpText = "Any arguments following '--' will be passed to the dafny CLI unaltered.")]
  public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();

  [Option("run-fails", HelpText = "Whether the running program should return a non-zero exit code")]
  public bool RunShouldFail { get; set; } = false;

  [Option("refresh-exit-code", HelpText = "If present, also run with --type-system-refresh and expect the given exit code.")]
  public int? RefreshExitCode { get; set; } = null;

  [Option("compilers", HelpText = "Test on only the given compilers.")]
  public string? Compilers { get; set; } = null;
}

[Verb("features", HelpText = "Print the Markdown content documenting feature support for each compiler.")]
public class FeaturesOptions {
  [Value(1)]
  public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
}

[Verb("for-each-resolver", HelpText = "For each resolver (legacy and refresh), execute the given test file, and assert the output matches the <test file>.expect file.")]
public class ForEachResolverOptions {

  [Value(0, Required = true, MetaName = "Test file", HelpText = "The *.dfy file to test.")]
  public string? TestFile { get; set; } = null;

  [Option("dafny", HelpText = "The dafny CLI to test with. Defaults to the locally built DafnyDriver project.")]
  public string? DafnyCliPath { get; set; } = null;

  [Value(1, MetaName = "Dafny CLI arguments", HelpText = "Any arguments following '--' will be passed to the dafny CLI unaltered.")]
  public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();

  [Option("expect-exit-code", HelpText = "Expected exit code for legacy resolver (default 0).")]
  public int? ExpectExitCode { get; set; } = null;

  [Option("refresh-exit-code", HelpText = "Expected exit code for refresh resolver (default expect-exit-code).")]
  public int? RefreshExitCode { get; set; } = null;
}

public class MultiBackendTest {
  private static readonly Assembly DafnyAssembly = typeof(Dafny.Dafny).Assembly;
  private readonly TextReader input;
  private readonly TextWriter output;
  private readonly TextWriter errorWriter;

  private static readonly string? IntegrationTestsRootDir =
    Environment.GetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_ROOT_DIR");
  private static readonly bool UpdateTargetExpectFile = DiffCommand.UpdateExpectFile;

  public MultiBackendTest(TextReader input, TextWriter output, TextWriter errorWriter) {
    this.input = input;
    this.output = output;
    this.errorWriter = errorWriter;
  }

  public static Task<int> Main(string[] args) {
    return new MultiBackendTest(Console.In, Console.Out, Console.Error).Start(args.ToList());
  }

  public Task<int> Start(IEnumerable<string> args) {
    var result = Task.FromResult(-1);
    var parser = new CommandLine.Parser(with => {
      with.EnableDashDash = true;
      with.HelpWriter = errorWriter;
    });
    var parseResult = parser.ParseArguments<ForEachCompilerOptions, FeaturesOptions, ForEachResolverOptions>(args);
#pragma warning disable VSTHRD002
    parseResult.WithParsed<ForEachCompilerOptions>(options => { result = ForEachCompiler(options); })
#pragma warning restore VSTHRD002
      .WithParsed<FeaturesOptions>(options => { result = Task.FromResult(GenerateCompilerTargetSupportTable(options)); })
      .WithParsed<ForEachResolverOptions>(options => { result = ForEachResolver(options); });

    return result;
  }

  private DafnyOptions? ParseDafnyOptions(IEnumerable<string> dafnyArgs) {
    var dafnyOptions = new DafnyOptions(input, output, errorWriter);
    var success = dafnyOptions.Parse(dafnyArgs.ToArray());
    return success ? dafnyOptions : null;
  }

  record ResolutionSetting(
    string ReadableName,
    string[] AdditionalOptions,
    string[] ExpectFileSuffixes,
    int ExpectedExitCode
  );

  private async Task<int> ForEachCompiler(ForEachCompilerOptions options) {
    var pluginParseResult = CommonOptionBag.PluginOption.Parse(options.OtherArgs.ToArray());
    var pluginArguments = pluginParseResult.GetValueForOption(CommonOptionBag.PluginOption);
    var plugins = DafnyOptions.ComputePlugins(new List<Plugin>(), pluginArguments ?? new List<string>());

    string rawCompilerFilter = options.Compilers ??
                               Environment.GetEnvironmentVariable("DAFNY_INTEGRATION_TESTS_ONLY_COMPILERS")
                               ?? "";
    string[] compilerFilter = rawCompilerFilter
      .Split(",")
      .Where(name => name.Trim() != "").ToArray();


    // First verify the file (and assume that verification should be successful).
    // Older versions of test files that now use %testDafnyForEachCompiler were sensitive to the number
    // of verification conditions (i.e. the X in "Dafny program verifier finished with X verified, 0 errors"),
    // but this was never meaningful and only added maintenance burden.
    // Here we only ensure that the exit code is 0.

    // We also use --(r|b)print to catch bugs with valid but unprintable programs.
    string fileName = Path.GetFileName(options.TestFile!);
    var testDir = Path.GetDirectoryName(options.TestFile!);
    var tmpDPrint = Path.Join(testDir, "Output", $"{fileName}.dprint");
    var tmpRPrint = Path.Join(testDir, "Output", $"{fileName}.rprint");
    var tmpPrint = Path.Join(testDir, "Output", $"{fileName}.print");

    var dafnyArgs = new List<string>() {
      $"verify",
      options.TestFile!,
      $"--print:{tmpDPrint}",
      options.OtherArgs.Any(option => option.StartsWith("--print")) ? "" : $"--rprint:{tmpRPrint}",
      $"--bprint:{tmpPrint}"
    }.Concat(DafnyCliTests.NewDefaultArgumentsForTesting).ToArray();

    var resolutionOptions = new List<ResolutionSetting>() {
      new ResolutionSetting(
        "legacy",
        new string[] { "--type-system-refresh=false", "--general-traits=legacy", "--general-newtypes=false" },
        new string[] { ".verifier.expect" },
        0)
    };
    if (options.RefreshExitCode != null) {
      resolutionOptions.Add(
        new ResolutionSetting(
          "refresh",
          new string[] { "--type-system-refresh" },
          new string[] { ".refresh.expect", ".verifier.expect" },
          (int)options.RefreshExitCode)
      );
    }

    foreach (var resolutionOption in resolutionOptions) {
      await output.WriteLineAsync($"Using {resolutionOption.ReadableName} resolver and verifying...");

      var arguments = dafnyArgs
        .Concat(resolutionOption.AdditionalOptions)
        .Concat(options.OtherArgs.Where(OptionAppliesToVerifyCommand))
        .ToArray();
      var (exitCode, outputString, error) = await RunDafny(options.DafnyCliPath, arguments);

      // If there is a file with extension "suffix", where the alternatives for "suffix" are supplied in order in
      // ExpectFileSuffixes, then we expect the output to match the contents of that file. Otherwise, we expect the output to be empty.
      var expectedOutput = "";
      foreach (var expectFileSuffix in resolutionOption.ExpectFileSuffixes) {
        var expectFileForVerifier = $"{options.TestFile}{expectFileSuffix}";
        if (File.Exists(expectFileForVerifier)) {
          expectedOutput = await File.ReadAllTextAsync(expectFileForVerifier);
          break;
        }
      }

      // Chop off the "Dafny program verifier finished with..." trailer
      var trailer = new Regex("\r?\nDafny program verifier[^\r\n]*\r?\n").Match(outputString);
      var actualOutput = outputString.Remove(trailer.Index, trailer.Length);
      var diffMessage = AssertWithDiff.GetDiffMessage(expectedOutput, actualOutput);
      if (diffMessage != null) {
        await output.WriteLineAsync(diffMessage);
        return 1;
      }

      // We expect verification to return exit code 0.
      if (exitCode != resolutionOption.ExpectedExitCode) {
        await output.WriteLineAsync(
          $"Verification failed with exit code {exitCode} (expected {resolutionOption.ExpectedExitCode}). Output:");
        await output.WriteLineAsync(outputString);
        await output.WriteLineAsync("Error:");
        await output.WriteLineAsync(error);
        return exitCode != 0 ? exitCode : 1;
      }
    }

    // Then execute the program for each available compiler.

    string expectFile = options.TestFile + ".expect";
    var commonExpectedOutput = await File.ReadAllTextAsync(expectFile);

    var success = true;
    foreach (var plugin in plugins) {
      foreach (var compiler in plugin.GetCompilers(DafnyOptions.Default)) {
        if (!compiler.IsStable || compilerFilter.Any() && !compilerFilter.Contains(compiler.TargetId)) {
          continue;
        }

        // Check for backend-specific exceptions (because of known bugs or inconsistencies)
        var expectedOutput = commonExpectedOutput;
        string? checkFile = null;
        var expectFileForBackend = ExpectFileForBackend(options, compiler);
        if (File.Exists(expectFileForBackend)) {
          expectedOutput = await File.ReadAllTextAsync(expectFileForBackend);
        }

        var checkFileForBackend = CheckFileForBackend(options, compiler);
        if (File.Exists(checkFileForBackend)) {
          checkFile = checkFileForBackend;
        } else if (GetSourceCheckFile(checkFileForBackend, out var originalCheckFile)) {
          checkFile = originalCheckFile;
        }

        var result = await RunWithCompiler(options, compiler, expectedOutput, checkFile);
        if (result != 0) {
          success = false;
        }

        if (compiler.TargetId == "cs") {
          // C# is a bit unusual in that the runtime behaves a little differently
          // depending on whether it is included as source or referenced as DafnyRuntime.dll
          // (because of "#ifdef ISDAFNYRUNTIMELIB" directives - see DafnyRuntime.cs).
          // This should be enabled for any other backends that have similar divergence.
          result = await RunWithCompiler(options, compiler, expectedOutput, checkFile, false);
          if (result != 0) {
            success = false;
          }
        }
      }
    }

    if (success) {
      await output.WriteLineAsync(
        "All executions were successful and matched the expected output (or reported errors for known unsupported features)!");
      return 0;
    }

    return -1;
  }

  private static bool GetSourceCheckFile(string checkFileForBackend, out string originalCheckFile) {
    if (IntegrationTestsRootDir is var x && !string.IsNullOrEmpty(x)
        && Path.Combine(x, checkFileForBackend) is var s && File.Exists(s)) {
      originalCheckFile = s;
      return true;
    } else {
      originalCheckFile = "";
      return false;
    }
  }

  private static string CheckFileForBackend(ForEachCompilerOptions options, IExecutableBackend compiler) {
    return $"{options.TestFile}.{compiler.TargetId}.check";
  }

  private static string ExpectFileForBackend(ForEachCompilerOptions options, IExecutableBackend compiler) {
    return $"{options.TestFile}.{compiler.TargetId}.expect";
  }

  public async Task<int> ForEachResolver(ForEachResolverOptions options) {
    // We also use --(r|b)print to catch bugs with valid but unprintable programs.
    string fileName = Path.GetFileName(options.TestFile!);
    var testDir = Path.GetDirectoryName(options.TestFile!);
    var tmpDPrint = Path.Join(testDir, "Output", $"{fileName}.dprint");
    var tmpRPrint = Path.Join(testDir, "Output", $"{fileName}.rprint");
    var tmpPrint = Path.Join(testDir, "Output", $"{fileName}.print");

    var dafnyArgs = new List<string>() {
      $"verify",
      options.TestFile!,
      $"--print:{tmpDPrint}",
      options.OtherArgs.Any(option => option.StartsWith("--print")) ? "" : $"--rprint:{tmpRPrint}",
      $"--bprint:{tmpPrint}"
    }.Concat(DafnyCliTests.NewDefaultArgumentsForTesting).ToArray();

    var resolutionOptions = new List<ResolutionSetting>() {
      new("legacy", new string[] { "--type-system-refresh=false", "--general-traits=legacy", "--general-newtypes=false" },
        new string[] { ".expect" },
        options.ExpectExitCode ?? 0),
      new("refresh", new string[] { "--type-system-refresh" },
        new string[] { ".refresh.expect", ".expect" },
        options.RefreshExitCode ?? options.ExpectExitCode ?? 0)
    };

    foreach (var resolutionOption in resolutionOptions) {
      await output.WriteLineAsync($"Using {resolutionOption.ReadableName} resolver and verifying...");

      var arguments = dafnyArgs
        .Concat(resolutionOption.AdditionalOptions)
        .Concat(options.OtherArgs.Where(OptionAppliesToVerifyCommand))
        .ToArray();
      var (exitCode, actualOutput, error) = await RunDafny(options.DafnyCliPath, arguments);

      // The expected output is indicated by a file with extension "suffix", where the alternatives for "suffix" are supplied in order in
      // ExpectFileSuffixes.
      string? expectFile = resolutionOption.ExpectFileSuffixes.
        Select(expectFileSuffix => $"{options.TestFile}{expectFileSuffix}").
        FirstOrDefault(File.Exists);
      if (expectFile == null) {
        var expectFileDescription = resolutionOption.ExpectFileSuffixes.Comma(suffix => $"{options.TestFile}{suffix}");
        await output.WriteLineAsync($"Missing expect file: {expectFileDescription}");
        return 1;
      }

      // Compare the output
      var diffMessage = DiffCommand.Run(expectFile, actualOutput);
      if (diffMessage != null) {
        await output.WriteLineAsync(diffMessage);
        return 1;
      }

      // We expect verification to return the indicated exit code.
      if (exitCode != resolutionOption.ExpectedExitCode) {
        await output.WriteLineAsync($"Verification failed with exit code {exitCode} (expected {resolutionOption.ExpectedExitCode}). Output:");
        await output.WriteLineAsync(actualOutput);
        await output.WriteLineAsync("Error:");
        await output.WriteLineAsync(error);
        return exitCode != 0 ? exitCode : 1;
      }
    }

    return 0; // success
  }

  // Necessary to avoid passing invalid options to the first `dafny verify` command.
  // Ideally we could hook into the general `dafny` options parsing logic
  // and `ICommandSpec` commands instead.
  private static bool OptionAppliesToVerifyCommand(string option) {
    var name = option[2..].Split(':')[0];

    var compileOptions = new List<Option> {
      CommonOptionBag.SpillTranslation,
      CommonOptionBag.OptimizeErasableDatatypeWrapper,
      CommonOptionBag.AddCompileSuffix,
      RunCommand.MainOverride,
    }.Select(o => o.Name);

    return !compileOptions.Contains(name);
  }

  private async Task<int> RunWithCompiler(ForEachCompilerOptions options, IExecutableBackend backend, string expectedOutput,
    string? checkFile, bool includeRuntime = true) {
    var expectFailure = options.RunShouldFail;
    await output.WriteAsync($"Executing on {backend.TargetName}");
    if (!includeRuntime) {
      await output.WriteAsync(" (with --include-runtime:false)");
    }
    await output.WriteLineAsync("...");

    // Build to a dedicated temporary directory to make sure tests don't interfere with each other.
    // The path will be something like "<user temp directory>/<random name>/<random name>"
    // to ensure that all artifacts are put in a dedicated directory,
    // which just "<user temp directory>/<random name>" would not.
    var randomDirectory = Path.ChangeExtension(Path.GetRandomFileName(), null);
    var randomFilename = Path.ChangeExtension(Path.GetRandomFileName(), null);
    // Attempts at making this path longer will likely crash javac on Windows with issues like "path too long"
    var tempOutputDirectory = Path.Combine(Path.GetTempPath(), randomDirectory);
    Directory.CreateDirectory(tempOutputDirectory);

    IEnumerable<string> dafnyArgs = new List<string> {
      "run",
      "--no-verify",
      "--emit-uncompilable-code",
      $"--target:{backend.TargetId}",
      $"--build:{Path.Combine(tempOutputDirectory, randomFilename)}",
      options.TestFile!,
    }.Concat(DafnyCliTests.NewDefaultArgumentsForTesting).Concat(options.OtherArgs);
    if (!includeRuntime) {
      // We have to provide the path to DafnyRuntime.dll manually, since the program will be run
      // in the directory containing the DLL built from Dafny code, not the Dafny distribution.
      if (backend.TargetId != "cs") {
        throw new ArgumentException("--include-runtime:false is currently only supported for the C# backend");
      }
      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      var runtimePath = Path.Join(libPath, "DafnyRuntime.dll");
      dafnyArgs = dafnyArgs.Concat(new[] { "--include-runtime:false", "--input", runtimePath });
      Directory.Delete(tempOutputDirectory);
    }

    int exitCode;
    string outputString;
    string error;
    try {
      (exitCode, outputString, error) = await RunDafny(options.DafnyCliPath, dafnyArgs);
    } catch (Exception e) {
      // When DAFNY_INTEGRATION_TESTS_IN_PROCESS is set to true, Dafny runs in the same process
      // so we catch the exception manually
      (exitCode, outputString, error) = (3, "", e.ToString());
    }

    var compilationOutputPrior = new Regex("\r?\nDafny program verifier[^\r\n]*\r?\n").Match(outputString);
    if (compilationOutputPrior.Success) {
      outputString = outputString.Remove(0, compilationOutputPrior.Index + compilationOutputPrior.Length);
    }

    var exitCodeAsExpected = expectFailure == (exitCode != 0);
    var diffMessage = exitCodeAsExpected ? AssertWithDiff.GetDiffMessage(expectedOutput, outputString) : null;
    if (checkFile == null && !exitCodeAsExpected) {
      if (UpdateTargetExpectFile && backend.TargetName != "dfy") {
        if (string.IsNullOrEmpty(IntegrationTestsRootDir)) {
          await output.WriteLineAsync(
            "DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE is true but DAFNY_INTEGRATION_TESTS_ROOT_DIR is not set");
        } else {
          return await UpdateBackendCheckFile(options, backend, expectedOutput, outputString, error, exitCode, false);
        }
      }
    }

    if (exitCodeAsExpected) {
      if (diffMessage != null) {
        await output.WriteLineAsync(diffMessage);
        if (backend.IsInternal) {
          await output.WriteLineAsync(
            $"(non-blocking) The {backend.TargetName} code generator is internal. Not having a '*.{backend.TargetId}.check' file is acceptable for now.");
          return 0;
        }

        // If we hit errors, check for known unsupported features or bugs for this compilation target
        if (error == "" && OnlyAllowedOutputLines(backend, outputString)) {
          return 0;
        }
        // If we hit errors, check for known unsupported features or bugs for this compilation target
        if (outputString == "" && OnlyAllowedOutputLines(backend, error)) {
          return 0;
        }

        return 1;
      }

      if (checkFile != null) {
        // The test now works, we delete the check file
        if (UpdateTargetExpectFile) {
          if ((IntegrationTestsRootDir ?? "") == "") {
            await output.WriteLineAsync(
              "DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE is true but DAFNY_INTEGRATION_TESTS_ROOT_DIR is not set");
          } else {
            var sourcePath = Path.Join(IntegrationTestsRootDir,
              CheckFileForBackend(options, backend));
            File.Delete(sourcePath);
          }
        }
      }
      return 0;
    }

    // If we hit errors, check for known unsupported features or bugs for this compilation target
    if (error == "" && OnlyAllowedOutputLines(backend, outputString)) {
      return 0;
    }
    // If we hit errors, check for known unsupported features or bugs for this compilation target
    if (outputString == "" && OnlyAllowedOutputLines(backend, error)) {
      return 0;
    }

    if (checkFile != null) {
      var outputLines = new List<string>();
      // Concatenate stdout and stderr so either can be checked against
      outputLines.AddRange(ReadAllLines(outputString));
      outputLines.AddRange(ReadAllLines(error));
      var checkDirectives = OutputCheckCommand.ParseCheckFile(checkFile);
      var checkResult = OutputCheckCommand.Execute(errorWriter, outputLines, checkDirectives);
      if (checkResult != 0) {
        await output.WriteLineAsync($"OutputCheck on {checkFile} failed. Output was:");
        await output.WriteLineAsync(string.Join("\n", outputLines));

        if (UpdateTargetExpectFile) {
          if (string.IsNullOrEmpty(IntegrationTestsRootDir)) {
            await output.WriteLineAsync(
              "DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE is true but DAFNY_INTEGRATION_TESTS_ROOT_DIR is not set");
          } else {
            return await UpdateBackendCheckFile(options, backend, expectedOutput, outputString, error, exitCode, true);
          }
        }
      }

      if (backend.IsInternal && checkResult != 0) {
        await output.WriteLineAsync(
          $"(non-blocking) The {backend.TargetName} code generator is internal. An unmatched '*.{backend.TargetId}.check' file is acceptable for now.");
        return 0;
      }

      return checkResult;
    }


    if (backend.IsInternal) {
      await output.WriteLineAsync($"(non-blocking) Execution failed for the internal {backend.TargetName} code generator, for reasons other than known unsupported features. Output:");
      await output.WriteLineAsync(outputString);
      await output.WriteLineAsync("Error:");
      await output.WriteLineAsync(error);
      await output.WriteLineAsync(
        $"The {backend.TargetName} code generator is internal. An unmatched '*.{backend.TargetId}.check' file is acceptable for now.");
      return 0;
    }
    await output.WriteLineAsync("Execution failed, for reasons other than known unsupported features. Output:");
    await output.WriteLineAsync(outputString);
    await output.WriteLineAsync("Error:");
    await output.WriteLineAsync(error);
    return exitCode;
  }

  private async Task<int> UpdateBackendCheckFile(ForEachCompilerOptions options, IExecutableBackend backend,
    string expectedOutput, string outputString, string error, int exitCode, bool expectedCheckFile) {
    var sourcePath = Path.Join(IntegrationTestsRootDir,
      CheckFileForBackend(options, backend));
    // outputString == error iff something crashed
    var contentCheck = outputString == error ? outputString.Trim() : (outputString + "\n" + error).Trim();
    var checkOutput = "";
    var shouldSuffice = true;
    if (contentCheck == "") {
      shouldSuffice = false;
      checkOutput = string.Join("\n",
        expectedOutput.Split("\n").Select(line => "// CHECK-NOT: " + line));
    } else {
      // A few heuristics to create the .ext.check files
      if (new Regex("<i>.*?</i>").Matches(contentCheck) is { Count: > 0 } m1) {
        checkOutput = "// CHECK: .*" + Regex.Escape(m1[0].Value.Trim()) + ".*";
      } else if (new Regex("<i>.*").Matches(contentCheck) is { Count: > 0 } m2) {
        checkOutput = "// CHECK: .*" + Regex.Escape(m2[0].Value.Trim()) + ".*";
      } else if (new Regex("^Unhandled exception.*$", RegexOptions.Multiline).Matches(contentCheck) is { Count: > 0 } m3) {
        checkOutput = "// CHECK-L: " + m3[0].Value.Trim();
      } else if (new Regex(@"^(error(?:\[\w+\])?:(?: \w+)*).*$", RegexOptions.Multiline).Matches(contentCheck) is { Count: > 0 } m4) {
        checkOutput = "// CHECK-L: " + m4[0].Value.Trim();
      } else {
        shouldSuffice = false;
        checkOutput = string.Join("\n",
          contentCheck.Split("\n")
            .Where(line => line != "")
            .Select(line => "// CHECK-L: " + line));
      }
    }

    if (!File.Exists(sourcePath) || expectedCheckFile) {
      await File.WriteAllTextAsync(sourcePath, checkOutput);
      if (shouldSuffice) {
        await output.WriteLineAsync(
          $"The new .check file {sourcePath} should capture this error. Please relaunch this test");
      } else {
        await output.WriteLineAsync(
          $"Please modify the new check file {sourcePath} so that it's valid no matter what.");
      }
    } else {
      await output.WriteLineAsync(
        $"Apparently, the file {sourcePath} already exists so the process isn't going to create one " +
        $" despite DAFNY_INTEGRATION_TESTS_UPDATE_EXPECT_FILE set to true and the file {CheckFileForBackend(options, backend)} not existing.\n" +
        " To avoid this message, please rebuild the solution (modifying a .cs file or a .dfy can help).");
    }

    await output.WriteLineAsync(outputString);
    await output.WriteLineAsync("Error:");
    await output.WriteLineAsync(error);

    return exitCode;
  }

  public static IList<string> ReadAllLines(string s) {
    var result = new List<string>();
    var reader = new StringReader(s);
    while (reader.ReadLine() is { } line) {
      result.Add(line);
    }
    return result;
  }
  private static async Task<(int, string, string)> RunDafny(IEnumerable<string> arguments) {
    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var exitCode = await DafnyBackwardsCompatibleCli.MainWithWriters(outputWriter, errorWriter, TextReader.Null, arguments.ToArray());
    var outputString = outputWriter.ToString();
    var error = errorWriter.ToString();
    return (exitCode, outputString, error);
  }

  private static async Task<(int, string, string)> RunDafny(string? dafnyCliPath, IEnumerable<string> arguments) {
    if (dafnyCliPath == null) {
      return await RunDafny(arguments);
    }

    ILitCommand command = new ShellLitCommand(dafnyCliPath, arguments, DafnyCliTests.ReferencedEnvironmentVariables);

    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var exitCode = await command.Execute(TextReader.Null, outputWriter, errorWriter);
    return (exitCode, outputWriter.ToString(), errorWriter.ToString());
  }

  private static bool OnlyAllowedOutputLines(IExecutableBackend backend, string output) {
    var prefixRecoverable = output.IndexOf(typeof(UnsupportedInvalidOperationException).FullName!, StringComparison.Ordinal);
    if (prefixRecoverable > 0) {
      return true;
    }
    prefixRecoverable = output.IndexOf(typeof(RecoverableUnsupportedFeatureException).FullName!, StringComparison.Ordinal);
    if (prefixRecoverable > 0) {
      return true;
    }

    using StringReader sr = new StringReader(output);
    if (output == "") {
      return false;
    }
    while (sr.ReadLine() is { } line) {
      if (!IsAllowedOutputLine(backend, line)) {
        return false;
      }
    }

    return true;
  }

  private static bool IsAllowedOutputLine(IExecutableBackend backend, string line) {
    line = line.Trim();
    if (line.Length == 0) {
      return true;
    }

    // This is output if the compiler emits any errors
    if (line.StartsWith("Translation was aborted")) {
      return true;
    }

    // This is output if included files have errors,
    // which is expected if we're including another test file and testing different CLI options
    if (Regex.IsMatch(line, "Error: the included file .* contains error\\(s\\)")) {
      return true;
    }

    var prefixIndex = line.IndexOf(UnsupportedFeatureException.MessagePrefix, StringComparison.Ordinal);
    if (prefixIndex < 0) {
      return false;
    }

    var featureDescription = line[(prefixIndex + UnsupportedFeatureException.MessagePrefix.Length)..];
    if (featureDescription.IndexOf(RecoverableUnsupportedFeatureException.MessageSuffix) is var i and > 0) {
      featureDescription = featureDescription[..i];
    }
    var feature = FeatureDescriptionAttribute.ForDescription(featureDescription);
    if (backend.UnsupportedFeatures.Contains(feature)) {
      return true;
    }

    // This is an internal inconsistency error
    throw new Exception(
      $"Compiler rejected feature '{feature}', which is not an element of its UnsupportedFeatures set");
  }

  private int GenerateCompilerTargetSupportTable(FeaturesOptions featuresOptions) {
    var dafnyOptions = ParseDafnyOptions(featuresOptions.OtherArgs);
    if (dafnyOptions == null) {
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var allCompilers = dafnyOptions.Plugins
      .SelectMany(p => p.GetCompilers(dafnyOptions))
      .Where(c => !c.IsInternal)
      .ToList();

    // Header
    output.Write("| Feature |");
    foreach (var compiler in allCompilers) {
      output.Write($" {compiler.TargetName} |");
    }

    output.WriteLine();

    // Horizontal rule ("|----|---|...")
    output.Write("|-|");
    foreach (var _ in allCompilers) {
      output.Write($"-|");
    }

    output.WriteLine();

    var footnotes = new StringBuilder();
    foreach (var feature in Enum.GetValues(typeof(Feature)).Cast<Feature>()) {
      var description = FeatureDescriptionAttribute.GetDescription(feature);
      var footnoteLink = "";
      if (description.FootnoteIdentifier != null) {
        footnoteLink = $"[^{description.FootnoteIdentifier}]";
        footnotes.AppendLine($"{footnoteLink}: {description.Footnote}");
        footnotes.AppendLine();
      }

      output.Write($"| [{description.Description}](#{description.ReferenceManualSection}){footnoteLink} |");
      foreach (var compiler in allCompilers) {
        var supported = !compiler.UnsupportedFeatures.Contains(feature);
        var cell = supported ? " X " : "";
        output.Write($" {cell} |");
      }

      output.WriteLine();
    }

    output.WriteLine();
    output.WriteLine(footnotes);

    return 0;
  }
}
