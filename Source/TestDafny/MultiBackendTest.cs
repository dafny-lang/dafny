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

  [Option("refresh-exit-code", HelpText = "If present, also run with --type-system-refresh and expect the given exit code.")]
  public int? RefreshExitCode { get; set; } = null;
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
    }.Concat(options.OtherArgs.Where(OptionAppliesToVerifyCommand)).ToArray();

    var resolutionOptions = new List<ResolutionSetting>() {
      new ResolutionSetting(
        "legacy",
        new string[] { },
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

      var (exitCode, outputString, error) = await RunDafny(options.DafnyCliPath, dafnyArgs.Concat(resolutionOption.AdditionalOptions));

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
        if (!compiler.IsStable) {
          // Some tests still fail when using the lib back-end, for example due to disallowed assumptions being present in the test,
          // Such as empty constructors with ensures clauses, generated from iterators
          continue;
        }

        // Check for backend-specific exceptions (because of known bugs or inconsistencies)
        var expectedOutput = commonExpectedOutput;
        string? checkFile = null;
        var expectFileForBackend = $"{options.TestFile}.{compiler.TargetId}.expect";
        if (File.Exists(expectFileForBackend)) {
          expectedOutput = await File.ReadAllTextAsync(expectFileForBackend);
        }

        var checkFileForBackend = $"{options.TestFile}.{compiler.TargetId}.check";
        if (File.Exists(checkFileForBackend)) {
          checkFile = checkFileForBackend;
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
    }.Concat(options.OtherArgs.Where(OptionAppliesToVerifyCommand)).ToArray();

    var resolutionOptions = new List<ResolutionSetting>() {
      new("legacy", new string[] { }, new string[] { ".expect" },
        options.ExpectExitCode ?? 0),
      new("refresh", new string[] { "--type-system-refresh" }, new string[] { ".refresh.expect", ".expect" },
        options.RefreshExitCode ?? options.ExpectExitCode ?? 0)
    };

    foreach (var resolutionOption in resolutionOptions) {
      await output.WriteLineAsync($"Using {resolutionOption.ReadableName} resolver and verifying...");

      var (exitCode, actualOutput, error) = await RunDafny(options.DafnyCliPath, dafnyArgs.Concat(resolutionOption.AdditionalOptions));

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
      BoogieOptionBag.SolverResourceLimit,
      BoogieOptionBag.VerificationTimeLimit,
      RunCommand.MainOverride,
    }.Select(o => o.Name);

    return !compileOptions.Contains(name);
  }

  private async Task<int> RunWithCompiler(ForEachCompilerOptions options, IExecutableBackend backend, string expectedOutput, string? checkFile, bool includeRuntime = true) {
    await output.WriteAsync($"Executing on {backend.TargetName}");
    if (!includeRuntime) {
      await output.WriteAsync(" (with --include-runtime:false)");
    }
    await output.WriteLineAsync("...");

    // Build to a dedicated temporary directory to make sure tests don't interfere with each other.
    // The path will be something like "<user temp directory>/<random name>/<random name>"
    // to ensure that all artifacts are put in a dedicated directory,
    // which just "<user temp directory>/<random name>" would not.
    var randomName = Path.ChangeExtension(Path.GetRandomFileName(), null);
    var tempOutputDirectory = Path.Combine(Path.GetTempPath(), randomName, randomName);
    Directory.CreateDirectory(tempOutputDirectory);

    IEnumerable<string> dafnyArgs = new List<string> {
      "run",
      "--no-verify",
      $"--target:{backend.TargetId}",
      $"--build:{tempOutputDirectory}",
      options.TestFile!,
    }.Concat(options.OtherArgs);
    if (!includeRuntime) {
      // We have to provide the path to DafnyRuntime.dll manually, since the program will be run
      // in the directory containing the DLL built from Dafny code, not the Dafny distribution.
      if (backend.TargetId != "cs") {
        throw new ArgumentException("--include-runtime:false is currently only supported for the C# backend");
      }
      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      var runtimePath = Path.Join(libPath, "DafnyRuntime.dll");
      dafnyArgs = dafnyArgs.Concat(new[] { "--include-runtime:false", "--input", runtimePath });
    }

    var (exitCode, outputString, error) = await RunDafny(options.DafnyCliPath, dafnyArgs);
    var compilationOutputPrior = new Regex("\r?\nDafny program verifier[^\r\n]*\r?\n").Match(outputString);
    if (compilationOutputPrior.Success) {
      outputString = outputString.Remove(0, compilationOutputPrior.Index + compilationOutputPrior.Length);
    }

    if (exitCode == 0) {
      var diffMessage = AssertWithDiff.GetDiffMessage(expectedOutput, outputString);
      if (diffMessage == null) {
        return 0;
      }

      await output.WriteLineAsync(diffMessage);
      return 1;
    }

    // If we hit errors, check for known unsupported features or bugs for this compilation target
    if (error == "" && OnlyUnsupportedFeaturesErrors(backend, outputString)) {
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
        await output.WriteLineAsync($"OutputCheck on {checkFile} failed:");
        await output.WriteLineAsync("Error:");
      }

      return checkResult;
    }

    await output.WriteLineAsync("Execution failed, for reasons other than known unsupported features. Output:");
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
    var argumentsWithDefaults = arguments.Concat(DafnyCliTests.NewDefaultArgumentsForTesting);
    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var exitCode = await DafnyBackwardsCompatibleCli.MainWithWriters(outputWriter, errorWriter, TextReader.Null, argumentsWithDefaults.ToArray());
    var outputString = outputWriter.ToString();
    var error = errorWriter.ToString();
    return (exitCode, outputString, error);
  }

  private static async Task<(int, string, string)> RunDafny(string? dafnyCliPath, IEnumerable<string> arguments) {
    if (dafnyCliPath == null) {
      return await RunDafny(arguments);
    }

    var argumentsWithDefaults = arguments.Concat(DafnyCliTests.NewDefaultArgumentsForTesting);
    ILitCommand command = new ShellLitCommand(dafnyCliPath, argumentsWithDefaults, DafnyCliTests.ReferencedEnvironmentVariables);

    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var exitCode = await command.Execute(TextReader.Null, outputWriter, errorWriter);
    return (exitCode, outputWriter.ToString(), errorWriter.ToString());
  }

  private static bool OnlyUnsupportedFeaturesErrors(IExecutableBackend backend, string output) {
    using StringReader sr = new StringReader(output);
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
    if (line.StartsWith("Wrote textual form of partial target program to")) {
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
