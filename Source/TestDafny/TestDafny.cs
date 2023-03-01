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

  [Value(1, MetaName = "Dafny CLI arguments", HelpText = "Any arguments following '--' will be passed to the dafny CLI unaltered.")] public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
}

[Verb("features", HelpText = "Print the Markdown content documenting feature support for each compiler.")]
public class FeaturesOptions {
  [Value(1)] public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
}

public class TestDafny {

  private static readonly Assembly DafnyAssembly = typeof(Dafny.Dafny).Assembly;

  public static int Main(string[] args) {
    var result = -1;
    var parser = new CommandLine.Parser(with => {
      with.EnableDashDash = true;
      with.HelpWriter = Console.Error;
    });
    var parseResult = parser.ParseArguments<ForEachCompilerOptions, FeaturesOptions>(args);
    parseResult.WithParsed<ForEachCompilerOptions>(options => {
      result = ForEachCompiler(options);
    }).WithParsed<FeaturesOptions>(options => {
      result = GenerateCompilerTargetSupportTable(options);
    });

    return result;
  }

  private static DafnyOptions? ParseDafnyOptions(IEnumerable<string> dafnyArgs) {
    var dafnyOptions = new DafnyOptions();
    var success = dafnyOptions.Parse(dafnyArgs.ToArray());
    return success ? dafnyOptions : null;
  }

  private static int ForEachCompiler(ForEachCompilerOptions options) {
    var dafnyOptions = ParseDafnyOptions(options.OtherArgs);
    if (dafnyOptions == null) {
      return (int)DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR;
    }

    // First verify the file (and assume that verification should be successful).
    // Older versions of test files that now use %testDafnyForEachCompiler were sensitive to the number
    // of verification conditions (i.e. the X in "Dafny program verifier finished with X verified, 0 errors"),
    // but this was never meaningful and only added maintenance burden.
    // Here we only ensure that the exit code is 0.

    var dafnyArgs = new List<string>(options.OtherArgs) {
      $"/compile:0",
      options.TestFile!
    };

    Console.Out.WriteLine("Verifying...");

    var (exitCode, output, error) = RunDafny(options.DafnyCliPath, dafnyArgs);
    if (exitCode != 0) {
      Console.Out.WriteLine("Verification failed. Output:");
      Console.Out.WriteLine(output);
      Console.Out.WriteLine("Error:");
      Console.Out.WriteLine(error);
      return exitCode;
    }

    // Then execute the program for each available compiler.

    string expectFile = options.TestFile + ".expect";
    var expectedOutput = "\nDafny program verifier did not attempt verification\n" +
                         File.ReadAllText(expectFile);

    var success = true;
    foreach (var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers(TODO)) {
        var result = RunWithCompiler(options, compiler, expectedOutput);
        if (result != 0) {
          success = false;
        }
      }
    }

    if (success) {
      Console.Out.WriteLine(
        $"All executions were successful and matched the expected output (or reported errors for known unsupported features)!");
      return 0;
    } else {
      return -1;
    }
  }

  private static int RunWithCompiler(ForEachCompilerOptions options, IExecutableBackend backend, string expectedOutput) {
    Console.Out.WriteLine($"Executing on {backend.TargetLanguage}...");
    var dafnyArgs = new List<string>(options.OtherArgs) {
      options.TestFile!,
      // Here we can pass /noVerify to save time since we already verified the program. 
      "/noVerify",
      // /noVerify is interpreted pessimistically as "did not get verification success",
      // so we have to force compiling and running despite this.
      "/compile:4",
      $"/compileTarget:{backend.TargetId}"
    };


    var (exitCode, output, error) = RunDafny(options.DafnyCliPath, dafnyArgs);
    if (exitCode == 0) {
      var diffMessage = AssertWithDiff.GetDiffMessage(expectedOutput, output);
      if (diffMessage == null) {
        return 0;
      }

      Console.Out.WriteLine(diffMessage);
      return 1;
    }

    // If we hit errors, check for known unsupported features for this compilation target
    if (error == "" && OnlyUnsupportedFeaturesErrors(backend, output)) {
      return 0;
    }

    Console.Out.WriteLine("Execution failed, for reasons other than known unsupported features. Output:");
    Console.Out.WriteLine(output);
    Console.Out.WriteLine("Error:");
    Console.Out.WriteLine(error);
    return exitCode;
  }

  private static (int, string, string) RunDafny(string? dafnyCLIPath, IEnumerable<string> arguments) {
    var argumentsWithDefaults = arguments.Concat(DafnyDriver.DefaultArgumentsForTesting);
    ILitCommand command;
    if (dafnyCLIPath != null) {
      command = new ShellLitCommand(dafnyCLIPath, argumentsWithDefaults, DafnyDriver.ReferencedEnvironmentVariables);
    } else {
      var dotnetArguments = new[] { DafnyAssembly.Location }.Concat(argumentsWithDefaults);
      command = new ShellLitCommand("dotnet", dotnetArguments, DafnyDriver.ReferencedEnvironmentVariables);
    }
    return command.Execute(null, null, null, null);
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

  private static int GenerateCompilerTargetSupportTable(FeaturesOptions featuresOptions) {
    var dafnyOptions = ParseDafnyOptions(featuresOptions.OtherArgs);
    if (dafnyOptions == null) {
      return (int)DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR;
    }

    // Header
    Console.Out.Write("| Feature |");
    var allCompilers = dafnyOptions.Plugins.SelectMany(p => p.GetCompilers(TODO)).ToList();
    foreach (var compiler in allCompilers) {
      Console.Out.Write($" {compiler.TargetLanguage} |");
    }

    Console.Out.WriteLine();

    // Horizontal rule ("|----|---|...")
    Console.Out.Write("|-|");
    foreach (var _ in allCompilers) {
      Console.Out.Write($"-|");
    }

    Console.Out.WriteLine();

    var footnotes = new StringBuilder();
    foreach (var feature in Enum.GetValues(typeof(Feature)).Cast<Feature>()) {
      var description = FeatureDescriptionAttribute.GetDescription(feature);
      var footnoteLink = "";
      if (description.FootnoteIdentifier != null) {
        footnoteLink = $"[^{description.FootnoteIdentifier}]";
        footnotes.AppendLine($"{footnoteLink}: {description.Footnote}");
        footnotes.AppendLine();
      }

      Console.Out.Write($"| [{description.Description}](#{description.ReferenceManualSection}){footnoteLink} |");
      foreach (var compiler in allCompilers) {
        var supported = !compiler.UnsupportedFeatures.Contains(feature);
        var cell = supported ? " X " : "";
        Console.Out.Write($" {cell} |");
      }

      Console.Out.WriteLine();
    }

    Console.Out.WriteLine();
    Console.Out.WriteLine(footnotes);

    return 0;
  }
}