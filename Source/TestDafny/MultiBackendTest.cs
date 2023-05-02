using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using CommandLine;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using XUnitExtensions;

namespace TestDafny;

[Verb("for-each-compiler", HelpText = "Execute the given test file for every compiler, and assert the output matches the <test file>.expect file.")]
public class ForEachCompilerOptions {

  [Value(0, Required = true, MetaName = "Test file", HelpText = "The *.dfy file to test.")]
  public string? TestFile { get; set; } = null;

  [Value(1, MetaName = "Dafny CLI arguments", HelpText = "Any arguments following '--' will be passed to the dafny CLI unaltered.")]
  public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
}

[Verb("features", HelpText = "Print the Markdown content documenting feature support for each compiler.")]
public class FeaturesOptions {
  [Value(1)] public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
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

  public static int Main(string[] args) {
    return new MultiBackendTest(Console.In, Console.Out, Console.Error).Start(args);
  }

  public int Start(IEnumerable<string> args) {
    var result = -1;
    var parser = new CommandLine.Parser(with => {
      with.EnableDashDash = true;
      with.HelpWriter = errorWriter;
    });
    var parseResult = parser.ParseArguments<ForEachCompilerOptions, FeaturesOptions>(args);
    parseResult.WithParsed<ForEachCompilerOptions>(options => { result = ForEachCompiler(options); })
      .WithParsed<FeaturesOptions>(options => { result = GenerateCompilerTargetSupportTable(options); });

    return result;
  }

  private DafnyOptions? ParseDafnyOptions(IEnumerable<string> dafnyArgs) {
    var dafnyOptions = new DafnyOptions(input, output, errorWriter);
    var success = dafnyOptions.Parse(dafnyArgs.ToArray());
    return success ? dafnyOptions : null;
  }

  private int ForEachCompiler(ForEachCompilerOptions options) {
    var parseResult = CommandRegistry.Create(TextWriter.Null, TextWriter.Null, TextReader.Null,
      new string[] { "verify", options.TestFile! }.Concat(options.OtherArgs).ToArray());
    var dafnyOptions = ((ParseArgumentSuccess)parseResult).DafnyOptions;

    // First verify the file (and assume that verification should be successful).
    // Older versions of test files that now use %testDafnyForEachCompiler were sensitive to the number
    // of verification conditions (i.e. the X in "Dafny program verifier finished with X verified, 0 errors"),
    // but this was never meaningful and only added maintenance burden.
    // Here we only ensure that the exit code is 0.

    var dafnyArgs = new List<string>() {
      $"verify",
      options.TestFile!
    }.Concat(options.OtherArgs).ToArray();

    output.WriteLine("Verifying...");

    var (exitCode, outputString, error) = RunDafny(dafnyArgs);
    if (exitCode != 0) {
      output.WriteLine("Verification failed. Output:");
      output.WriteLine(outputString);
      output.WriteLine("Error:");
      output.WriteLine(error);
      return exitCode;
    }

    // Then execute the program for each available compiler.

    string expectFile = options.TestFile + ".expect";
    var expectedOutput = "\nDafny program verifier did not attempt verification\n" +
                         File.ReadAllText(expectFile);

    var success = true;
    foreach (var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers(dafnyOptions)) {
        var result = RunWithCompiler(options, compiler, expectedOutput);
        if (result != 0) {
          success = false;
        }
      }
    }

    if (success) {
      output.WriteLine(
        $"All executions were successful and matched the expected output (or reported errors for known unsupported features)!");
      return 0;
    } else {
      return -1;
    }
  }

  private int RunWithCompiler(ForEachCompilerOptions options, IExecutableBackend backend, string expectedOutput) {
    output.WriteLine($"Executing on {backend.TargetName}...");
    var dafnyArgs = new List<string>() {
      "run",
      "--no-verify",
      $"--target:{backend.TargetId}",
      options.TestFile!,
    }.Concat(options.OtherArgs);

    var (exitCode, outputString, error) = RunDafny(dafnyArgs);

    if (exitCode == 0) {
      var diffMessage = AssertWithDiff.GetDiffMessage(expectedOutput, outputString);
      if (diffMessage == null) {
        return 0;
      }

      output.WriteLine(diffMessage);
      return 1;
    }

    // If we hit errors, check for known unsupported features for this compilation target
    if (error == "" && OnlyUnsupportedFeaturesErrors(backend, outputString)) {
      return 0;
    }

    output.WriteLine("Execution failed, for reasons other than known unsupported features. Output:");
    output.WriteLine(outputString);
    output.WriteLine("Error:");
    output.WriteLine(error);
    return exitCode;
  }

  private static (int, string, string) RunDafny(IEnumerable<string> arguments) {
    var argumentsWithDefaults = arguments.Concat(DafnyDriver.NewDefaultArgumentsForTesting);
    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var exitCode = DafnyDriver.MainWithWriter(outputWriter, errorWriter, TextReader.Null, argumentsWithDefaults.ToArray());
    var outputString = outputWriter.ToString();
    var error = errorWriter.ToString();
    return (exitCode, outputString, error);
  }

  private static bool OnlyUnsupportedFeaturesErrors(IExecutableBackend backend, string output) {
    using (StringReader sr = new StringReader(output)) {
      string? line;
      while ((line = sr.ReadLine()) != null) {
        if (!IsAllowedOutputLine(backend, line)) {
          return false;
        }
      }
    }

    return true;
  }

  private static bool IsAllowedOutputLine(IExecutableBackend backend, string line) {
    line = line.Trim();
    if (line.Length == 0) {
      return true;
    }

    // This is the first non-blank line we expect when we pass /noVerify
    if (line == "Dafny program verifier did not attempt verification") {
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
      return (int)DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR;
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
