using System;
using System.Collections.Generic;
using System.CommandLine.Help;
using System.CommandLine.Invocation;
using System.CommandLine.IO;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

public interface ILegacyParseArguments { }

// TODO: Refactor so that non-errors (NOT_VERIFIED, DONT_PROCESS_FILES) don't result in non-zero exit codes
public enum ExitValue { SUCCESS = 0, PREPROCESSING_ERROR, DAFNY_ERROR, COMPILE_ERROR, VERIFICATION_ERROR, FORMAT_ERROR }

public record ParsedOptions(DafnyOptions DafnyOptions) : ILegacyParseArguments;
record ExitImmediately(ExitValue ExitValue) : ILegacyParseArguments;

// TODO reduce usages
public static class DafnyBackwardsCompatibleCli {

  public static int Main(string[] args) {
    return MainWithWriters(Console.Out, Console.Error, Console.In, args);
  }

  public static int MainWithWriters(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader,
    string[] args) {
    // Code that shouldn't be needed, but prevents some exceptions when running the integration tests in parallel
    // outputWriter = new UndisposableTextWriter(outputWriter);
    // errorWriter = new UndisposableTextWriter(errorWriter);
    // outputWriter = TextWriter.Synchronized(outputWriter);
    // errorWriter = TextWriter.Synchronized(errorWriter);

#pragma warning disable VSTHRD002
    var exitCode = Task.Run(() => ThreadMain(outputWriter, errorWriter, inputReader, args)).Result;
    return exitCode;
#pragma warning restore VSTHRD002
  }

  private static Task<int> ThreadMain(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args) {
    Contract.Requires(cce.NonNullElements(args));
    return Execute(outputWriter, errorWriter, inputReader, args, async parseArgumentResult => {

      switch (parseArgumentResult) {
        case ParsedOptions success:
          var options = success.DafnyOptions;
          return await RunLegacyCompiler(options);
        case ExitImmediately failure:
          return (int)failure.ExitValue;
        default: throw new Exception("unreachable");
      }
    });
  }

  // TODO reduce useages
  public static async Task<int> RunLegacyCompiler(DafnyOptions options) {

    options.RunningBoogieFromCommandLine = true;

    var backend = GetBackend(options);
    if (backend == null) {
      return (int)ExitValue.PREPROCESSING_ERROR;
    }
    options.Backend = backend;

    var getFilesExitCode = GetDafnyFiles(options, out var dafnyFiles, out var otherFiles);
    if (getFilesExitCode != ExitValue.SUCCESS) {
      return (int)getFilesExitCode;
    }
    
    if (options.ExtractCounterexample && options.ModelViewFile == null) {
      options.Printer.ErrorWriteLine(options.OutputWriter,
        "*** Error: ModelView file must be specified when attempting counterexample extraction");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }
    
    using var driver = new CompilerDriver(options);
    ProofDependencyManager depManager = new();
    var exitValue = await driver.ProcessFilesAsync(dafnyFiles, otherFiles.AsReadOnly(), options, depManager);
    
    options.XmlSink?.Close();
    
    if (options.VerificationLoggerConfigs.Any()) {
      try {
        VerificationResultLogger.RaiseTestLoggerEvents(options, depManager);
      } catch (ArgumentException ae) {
        options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: {ae.Message}");
        exitValue = ExitValue.PREPROCESSING_ERROR;
      }
    }

    if (options.Wait) {
      Console.WriteLine("Press Enter to exit.");
      Console.ReadLine();
    }

    return (int)exitValue;
  }

  private static IExecutableBackend GetBackend(DafnyOptions options) {
    var backends = options.Plugins.SelectMany(p => p.GetCompilers(options)).ToList();
    var backend = backends.LastOrDefault(c => c.TargetId == options.CompilerName);
    if (backend == null) {
      if (options.CompilerName != null) {
        var known = String.Join(", ", backends.Select(c => $"'{c.TargetId}' ({c.TargetName})"));
        options.Printer.ErrorWriteLine(options.ErrorWriter,
          $"*** Error: No compiler found for target \"{options.CompilerName}\"{(options.CompilerName.StartsWith("-t") || options.CompilerName.StartsWith("--") ? " (use just a target name, not a -t or --target option)" : "")}; expecting one of {known}");
      } else {
        backend = new NoExecutableBackend(options);
      }
    }

    return backend;
  }

  private static async Task<int> Execute(TextWriter outputWriter,
    TextWriter errorWriter,
    TextReader inputReader, string[] arguments,
    Func<ILegacyParseArguments, Task<int>> onLegacyArguments) {

    var legacyResult = TryLegacyArgumentParser(inputReader, outputWriter, errorWriter, arguments);
    if (legacyResult != null) {
      return await onLegacyArguments(legacyResult);
    }

    return await DafnyCli.Execute(outputWriter, errorWriter, inputReader, arguments);
  }

  private static ILegacyParseArguments TryLegacyArgumentParser(
    TextReader inputReader,
    TextWriter outputWriter,
    TextWriter errorWriter,
    string[] arguments) {
    if (arguments.Length == 0) {
      return null;
    }
    var dafnyOptions = new DafnyOptions(inputReader, outputWriter, errorWriter) {
      Environment = "Command-line arguments: " + string.Join(" ", arguments)
    };

    var first = arguments[0];
    var keywordForNewMode = DafnyCli.RootCommand.Subcommands.Select(c => c.Name).Union(new[]
      { "--version", "-h", DafnyCli.ToolchainDebuggingHelpName, "--help", "[parse]", "[suggest]" });
    if (!keywordForNewMode.Contains(first)) {
      if (first.Length > 0 && first[0] != '/' && first[0] != '-' && !File.Exists(first) &&
          first.IndexOf('.') == -1) {
        dafnyOptions.Printer.ErrorWriteLine(dafnyOptions.OutputWriter,
          "*** Error: '{0}': The first input must be a command or a legacy option or file with supported extension",
          first);
        return new ExitImmediately(ExitValue.PREPROCESSING_ERROR);
      } else {
        var oldOptions = new DafnyOptions(dafnyOptions.Input, dafnyOptions.OutputWriter, dafnyOptions.ErrorWriter);
        try {
          if (oldOptions.Parse(arguments)) {
            // If requested, print version number, help, attribute help, etc. and exit.
            if (oldOptions.ProcessInfoFlags()) {
              return new ExitImmediately(ExitValue.SUCCESS);
            }

            return new ParsedOptions(oldOptions);
          }

          return new ExitImmediately(ExitValue.PREPROCESSING_ERROR);
        } catch (ProverException pe) {
          new DafnyConsolePrinter(dafnyOptions).ErrorWriteLine(dafnyOptions.OutputWriter,
            "*** ProverException: {0}", pe.Message);
          return new ExitImmediately(ExitValue.PREPROCESSING_ERROR);
        }
      }
    }

    return null;
  }

  public static ExitValue GetDafnyFiles(DafnyOptions options,
    out List<DafnyFile> dafnyFiles,
    out List<string> otherFiles) {

    if (options.DafnyProject != null) {
      foreach (var uri in options.DafnyProject.GetRootSourceUris(OnDiskFileSystem.Instance)) {
        options.CliRootSourceUris.Add(uri);
      }
    }

    dafnyFiles = new List<DafnyFile>();
    otherFiles = new List<string>();
    var outputWriter = options.OutputWriter;

    if (options.UseStdin) {
      var uri = new Uri("stdin:///");
      options.CliRootSourceUris.Add(uri);
      dafnyFiles.Add(DafnyFile.CreateAndValidate(new ConsoleErrorReporter(options), OnDiskFileSystem.Instance, options, uri, Token.NoToken));
    } else if (options.CliRootSourceUris.Count == 0) {
      options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: No input files were specified in command-line. " + options.Environment);
      return ExitValue.PREPROCESSING_ERROR;
    }
    if (options.XmlSink != null) {
      string errMsg = options.XmlSink.Open();
      if (errMsg != null) {
        options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: " + errMsg);
        return ExitValue.PREPROCESSING_ERROR;
      }
    }
    if (options.ShowEnv == ExecutionEngineOptions.ShowEnvironment.Always) {
      outputWriter.WriteLine(options.Environment);
    }

    ISet<String> filesSeen = new HashSet<string>();
    foreach (var file in options.CliRootSourceUris.Where(u => u.IsFile).Select(u => u.LocalPath).
               Concat(SplitOptionValueIntoFiles(options.LibraryFiles))) {
      Contract.Assert(file != null);
      var extension = Path.GetExtension(file);
      if (extension != null) { extension = extension.ToLower(); }

      bool isDafnyFile = false;
      var relative = Path.GetFileName(file);
      bool useRelative = options.UseBaseNameForFileName || relative.StartsWith("-");
      var nameToShow = useRelative ? relative
        : Path.GetRelativePath(Directory.GetCurrentDirectory(), file);
      try {
        var consoleErrorReporter = new ConsoleErrorReporter(options);
        var df = DafnyFile.CreateAndValidate(consoleErrorReporter, OnDiskFileSystem.Instance, options, new Uri(Path.GetFullPath(file)), Token.Cli);
        if (df == null) {
          if (consoleErrorReporter.HasErrors) {
            return ExitValue.PREPROCESSING_ERROR;
          }
        } else {
          if (options.LibraryFiles.Contains(file)) {
            df.IsPreverified = true;
            df.IsPrecompiled = true;
          }
          if (!filesSeen.Add(df.CanonicalPath)) {
            continue; // silently ignore duplicate
          }
          dafnyFiles.Add(df);
          isDafnyFile = true;
        }
      } catch (ArgumentException e) {
        options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: {0}: ", nameToShow, e.Message);
        return ExitValue.PREPROCESSING_ERROR;
      } catch (Exception e) {
        options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: {0}: {1}", nameToShow, e.Message);
        return ExitValue.PREPROCESSING_ERROR;
      }

      var supportedExtensions = options.Backend.SupportedExtensions;
      if (supportedExtensions.Contains(extension)) {
        // .h files are not part of the build, they are just emitted as includes
        // TODO: This should be delegated to the backend instead (i.e. the CppCompilerBackend)
        if (File.Exists(file) || extension == ".h") {
          otherFiles.Add(file);
        } else {
          options.Printer.ErrorWriteLine(options.OutputWriter, $"*** Error: file {nameToShow} not found");
          return ExitValue.PREPROCESSING_ERROR;
        }
      } else if (options.AllowSourceFolders && Directory.Exists(file)) {
        options.SourceFolders.Add(file);
      } else if (!isDafnyFile) {
        if (options.UsingNewCli && string.IsNullOrEmpty(extension) && file.Length > 0) {
          options.Printer.ErrorWriteLine(options.OutputWriter,
            "*** Error: Command-line argument '{0}' is neither a recognized option nor a filename with a supported extension ({1}).",
            nameToShow,
            string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions)));
        } else if (string.IsNullOrEmpty(extension) && file.Length > 0 && (file[0] == '/' || file[0] == '-')) {
          options.Printer.ErrorWriteLine(options.OutputWriter,
            "*** Error: Command-line argument '{0}' is neither a recognized option nor a filename with a supported extension ({1}).",
            nameToShow, string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions)));
        } else {
          options.Printer.ErrorWriteLine(options.OutputWriter,
            "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or supported auxiliary files ({2})",
            nameToShow, extension, string.Join(", ", supportedExtensions));
        }
        return ExitValue.PREPROCESSING_ERROR;
      }
    }

    if (dafnyFiles.Count == 0 && options.SourceFolders.Count == 0) {
      if (!options.AllowSourceFolders) {
        options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files");
        // TODO: With the test on CliRootUris.Count above, this code is no longer reachable
        options.Printer.ErrorWriteLine(options.OutputWriter, "*** Error: The command-line contains no .dfy files");
        return ExitValue.PREPROCESSING_ERROR;
      }

      options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files or folders");
      //options.Printer.ErrorWriteLine(Console.Out,
      //  "Usage:\ndafny format [--check] [--print] <file/folder> <file/folder>...\nYou can use '.' for the current directory");
      return ExitValue.PREPROCESSING_ERROR;
    }

    // Add standard library .doo files after explicitly provided source files,
    // only because if they are added first, one might be used as the program name,
    // which is not handled well.
    if (options.Get(CommonOptionBag.UseStandardLibraries)) {
      var reporter = new ConsoleErrorReporter(options);
      if (options.CompilerName is null or "cs" or "java" or "go" or "py" or "js") {
        var targetName = options.CompilerName ?? "notarget";
        var stdlibDooUri = new Uri($"{DafnyMain.StandardLibrariesDooUriBase}-{targetName}.doo");
        options.CliRootSourceUris.Add(stdlibDooUri);
        dafnyFiles.Add(DafnyFile.CreateAndValidate(reporter, OnDiskFileSystem.Instance, options, stdlibDooUri, Token.Cli));
      }

      options.CliRootSourceUris.Add(DafnyMain.StandardLibrariesDooUri);
      dafnyFiles.Add(DafnyFile.CreateAndValidate(reporter, OnDiskFileSystem.Instance, options, DafnyMain.StandardLibrariesDooUri, Token.Cli));

      options.CliRootSourceUris.Add(DafnyMain.StandardLibrariesArithmeticDooUri);
      dafnyFiles.Add(DafnyFile.CreateAndValidate(reporter, OnDiskFileSystem.Instance, options, DafnyMain.StandardLibrariesArithmeticDooUri, Token.Cli));
    }

    return ExitValue.SUCCESS;
  }

  static IEnumerable<string> SplitOptionValueIntoFiles(HashSet<string> inputs) {
    var result = new HashSet<string>();
    foreach (var input in inputs) {
      var values = input.Split(',');
      foreach (var slice in values) {
        var name = slice.Trim();
        if (Directory.Exists(name)) {
          var files = Directory.GetFiles(name, "*.dfy", SearchOption.AllDirectories);
          foreach (var file in files) { result.Add(file); }
        } else {
          result.Add(name);
        }
      }
    }
    return result;
  }
}