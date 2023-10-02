using System;
using System.Collections;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Help;
using System.CommandLine.Invocation;
using System.CommandLine.IO;
using System.CommandLine.Parsing;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using DafnyCore;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer;

namespace Microsoft.Dafny;

public interface IParseArgumentResult { }

// TODO: Refactor so that non-errors (NOT_VERIFIED, DONT_PROCESS_FILES) don't result in non-zero exit codes
public enum ExitValue { SUCCESS = 0, PREPROCESSING_ERROR, DAFNY_ERROR, COMPILE_ERROR, VERIFICATION_ERROR, FORMAT_ERROR }

public record ParseArgumentSuccess(DafnyOptions DafnyOptions) : IParseArgumentResult;
record ParseArgumentFailure(ExitValue ExitValue) : IParseArgumentResult;

public static class DafnyCli {
  private const string ToolchainDebuggingHelpName = "--help-internal";
  private static readonly RootCommand RootCommand = new("The Dafny CLI enables working with Dafny, a verification-aware programming language. Use 'dafny -?' to see help for the previous CLI format.");



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
    return Task.Run(() => ThreadMain(outputWriter, errorWriter, inputReader, args)).Result;
#pragma warning restore VSTHRD002
  }

  private static Task<int> ThreadMain(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args) {
    Contract.Requires(cce.NonNullElements(args));
    return DafnyCli.Execute(outputWriter, errorWriter, inputReader, args, async parseArgumentResult => {

      switch (parseArgumentResult) {
        case ParseArgumentSuccess success:
          var options = success.DafnyOptions;
          return await DafnyPipelineDriver.ContinueCliWithOptions(options);
        case ParseArgumentFailure failure:
          return (int)failure.ExitValue;
        default: throw new Exception("unreachable");
      }
    });
  }

  private static void AddCommand(Command command) {
    RootCommand.AddCommand(command);
  }

  static DafnyCli() {
    AddCommand(ResolveCommand.Create());
    AddCommand(VerifyCommand.Create());
    AddCommand(BuildCommand.Create());
    AddCommand(RunCommand.Create());
    AddCommand(TranslateCommand.Create());
    AddCommand(FormatCommand.Create());
    AddCommand(DocCommand.Create());
    AddCommand(MeasureComplexityCommand.Create());
    AddCommand(ServerCommand.Instance);
    AddCommand(TestCommand.Create());
    AddCommand(GenerateTestsCommand.Create());
    AddCommand(DeadCodeCommand.Create());
    AddCommand(AuditCommand.Create());
    AddCommand(CoverageReportCommand.Create());

    // Check that the .doo file format is aware of all options,
    // and therefore which have to be saved to safely support separate verification/compilation.
    DooFile.CheckOptions(AllOptions);

    FileArgument = new Argument<FileInfo>("file", "Dafny input file or Dafny project file");

    // This SHOULD find the same method but returns null for some reason:
    // typeof(ParseResult).GetMethod("GetValueForOption", 1, new[] { typeof(Option<>) });
    foreach (var method in typeof(ParseResult).GetMethods()) {
      if (method.Name == "GetValueForOption" && method.GetGenericArguments().Length == 1) {
        GetValueForOptionMethod = method;
      }
    }
    Debug.Assert(GetValueForOptionMethod != null);
  }

  public static Argument<FileInfo> FileArgument { get; }

  class WritersConsole : IConsole {
    public TextReader InputWriter { get; }
    public TextWriter ErrWriter { get; }
    public TextWriter OutWriter { get; }

    public WritersConsole(TextReader inputWriter, TextWriter outWriter, TextWriter errWriter) {
      InputWriter = inputWriter;
      this.ErrWriter = errWriter;
      this.OutWriter = outWriter;
    }

    public IStandardStreamWriter Out => StandardStreamWriter.Create(OutWriter ?? TextWriter.Null);

    public bool IsOutputRedirected => OutWriter != null;
    public IStandardStreamWriter Error => StandardStreamWriter.Create(ErrWriter ?? TextWriter.Null);
    public bool IsErrorRedirected => ErrWriter != null;
    public bool IsInputRedirected => false;
  }

  public delegate Task<int> ContinueWithOptions(DafnyOptions dafnyOptions, InvocationContext context);
  public static void SetHandlerUsingDafnyOptionsContinuation(Command command, ContinueWithOptions continuation) {

    var optionValues = new Dictionary<Option, object>();
    async Task Handle(InvocationContext context) {
      WritersConsole console = (WritersConsole)context.Console;
      var dafnyOptions = new DafnyOptions(console.InputWriter, console.OutWriter, console.ErrWriter);
      dafnyOptions.Environment =
        "Command-line arguments: " + string.Join(" ", context.ParseResult.Tokens.Select(t => t.Value));
      dafnyOptions.ShowEnv = ExecutionEngineOptions.ShowEnvironment.Never;
      var options = new Options(optionValues, new Dictionary<Argument, object>());
      dafnyOptions.Options = options;
      dafnyOptions.Command = command;

      var singleFile = context.ParseResult.GetValueForArgument(FileArgument);
      if (singleFile != null) {
        if (!await ProcessFile(dafnyOptions, singleFile)) {
          context.ExitCode = (int)ExitValue.PREPROCESSING_ERROR;
          return;
        }
      }
      var files = context.ParseResult.GetValueForArgument(Dafny.DafnyCommands.FilesArgument);
      if (files != null) {
        foreach (var file in files) {
          if (!await ProcessFile(dafnyOptions, file)) {
            context.ExitCode = (int)ExitValue.PREPROCESSING_ERROR;
            return;
          }
        }
      }

      foreach (var argument in command.Arguments) {
        var result = context.ParseResult.FindResultFor(argument)?.GetValueOrDefault();
        if (result != null) {
          options.Arguments[argument] = result;
        }
      }

      foreach (var option in command.Options) {
        var result = context.ParseResult.FindResultFor(option);
        object projectFileValue = null;
        var hasProjectFileValue = dafnyOptions.DafnyProject?.TryGetValue(option, dafnyOptions.ErrorWriter, out projectFileValue) ?? false;
        object value;
        if (option.Arity.MaximumNumberOfValues <= 1) {
          // If multiple values aren't allowed, CLI options take precedence over project file options
          value = (result == null || Equals(result.Token, null)) && hasProjectFileValue
            ? projectFileValue
            : GetValueForOption(context.ParseResult, option);
        } else {
          // If multiple values ARE allowed, CLI options come after project file options
          var elementType = option.ValueType.GetGenericArguments()[0];
          var valueAsList = (IList)Activator.CreateInstance(typeof(List<>).MakeGenericType(elementType))!;
          if (hasProjectFileValue) {
            foreach (var element in (IEnumerable)projectFileValue) {
              valueAsList.Add(element);
            }
          }
          if (result != null) {
            foreach (var element in (IEnumerable)GetValueForOption(context.ParseResult, option)) {
              valueAsList.Add(element);
            }
          }

          value = valueAsList;
        }

        options.OptionArguments[option] = value;
        try {
          dafnyOptions.ApplyBinding(option);
        } catch (Exception e) {
          context.ExitCode = (int)ExitValue.PREPROCESSING_ERROR;
          dafnyOptions.Printer.ErrorWriteLine(dafnyOptions.OutputWriter,
            $"Invalid value for option {option.Name}: {e.Message}");
          return;
        }
      }

      dafnyOptions.CurrentCommand = command;
      dafnyOptions.ApplyDefaultOptionsWithoutSettingsDefault();
      context.ExitCode = await continuation(dafnyOptions, context);
    }

    command.SetHandler(Handle);
  }

  public static Task<int> Execute(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] arguments,
    Func<IParseArgumentResult, Task<int>> afterArgumentParsing) {
    var dafnyOptions = new DafnyOptions(inputReader, outputWriter, errorWriter) {
      Environment = "Command-line arguments: " + string.Join(" ", arguments)
    };

    if (arguments.Length != 0) {
      var first = arguments[0];
      var keywordForNewMode = RootCommand.Subcommands.Select(c => c.Name).
        Union(new[] { "--version", "-h", ToolchainDebuggingHelpName, "--help", "[parse]", "[suggest]" });
      if (!keywordForNewMode.Contains(first)) {
        if (first.Length > 0 && first[0] != '/' && first[0] != '-' && !File.Exists(first) && first.IndexOf('.') == -1) {
          dafnyOptions.Printer.ErrorWriteLine(dafnyOptions.OutputWriter,
            "*** Error: '{0}': The first input must be a command or a legacy option or file with supported extension", first);
          return afterArgumentParsing(new ParseArgumentFailure(ExitValue.PREPROCESSING_ERROR));
        }

        var oldOptions = new DafnyOptions(inputReader, outputWriter, errorWriter);
        try {
          if (oldOptions.Parse(arguments)) {
            return afterArgumentParsing(new ParseArgumentSuccess(oldOptions));
          }

          // If requested, print version number, help, attribute help, etc. and exit.
          if (oldOptions.ProcessInfoFlags()) {
            return Task.FromResult((int)ExitValue.SUCCESS);
          }

          return afterArgumentParsing(new ParseArgumentFailure(ExitValue.PREPROCESSING_ERROR));
        } catch (ProverException pe) {
          new DafnyConsolePrinter(DafnyOptions.Create(outputWriter)).ErrorWriteLine(outputWriter, "*** ProverException: {0}", pe.Message);
          return afterArgumentParsing(new ParseArgumentFailure(ExitValue.PREPROCESSING_ERROR));
        }
      }
    }

    // bool allowHidden = arguments.All(a => a != ToolchainDebuggingHelpName);
    // foreach (var option in AllOptions) {
    //   if (!allowHidden) {
    //     option.IsHidden = false;
    //   }
    //   if (!option.Arity.Equals(ArgumentArity.ZeroOrMore) && !option.Arity.Equals(ArgumentArity.OneOrMore)) {
    //     option.AllowMultipleArgumentsPerToken = true;
    //   }
    // }
    //

    dafnyOptions.UsingNewCli = true;
    var builder = new CommandLineBuilder(RootCommand).UseDefaults();
    builder = AddDeveloperHelp(RootCommand, builder);
    var console = new WritersConsole(inputReader, outputWriter, errorWriter);
    return builder.Build().InvokeAsync(arguments, console);
  }

  private static readonly MethodInfo GetValueForOptionMethod;

  // This bit of reflective trickery is necessary because
  // ParseResult.GetValueForOption<T>(Option<T>) will convert tokens to T as necessary,
  // but ParseResult.GetValueForOption(Option) behaves like it was passed a Option<object> and doesn't.
  // To work around this we use reflection to invoke the former, passing Option.ValueType as the T argument.
  // This technique could also be used to fix the discrepancy between
  // DafnyOptions.Get<T>(Option<T>) and DafnyOptions.Get(Option)
  // (where in that case the latter doesn't set the default value).
  private static object GetValueForOption(ParseResult result, Option option) {
    // Use Reflection to invoke GetValueForOption<T> for the correct T
    var generic = GetValueForOptionMethod.MakeGenericMethod(option.ValueType);
    return generic.Invoke(result, new object[] { option });
  }

  private static async Task<bool> ProcessFile(DafnyOptions dafnyOptions, FileInfo singleFile) {
    var filePathForErrors = dafnyOptions.UseBaseNameForFileName
      ? Path.GetFileName(singleFile.FullName)
      : singleFile.FullName;
    if (Path.GetExtension(singleFile.FullName) == ".toml") {
      if (dafnyOptions.DafnyProject != null) {
        await dafnyOptions.ErrorWriter.WriteLineAsync($"Only one project file can be used at a time. Both {dafnyOptions.DafnyProject.Uri.LocalPath} and {filePathForErrors} were specified");
        return false;
      }

      if (!File.Exists(singleFile.FullName)) {
        await dafnyOptions.ErrorWriter.WriteLineAsync($"Error: file {filePathForErrors} not found");
        return false;
      }
      var projectFile = await DafnyProject.Open(OnDiskFileSystem.Instance, new Uri(singleFile.FullName));
      if (projectFile == null) {
        return false;
      }

      foreach (var diagnostic in projectFile.Errors.AllMessages) {
        var message = $"{diagnostic.Level}: {diagnostic.Message}";
        if (diagnostic.Level == ErrorLevel.Error) {
          await dafnyOptions.ErrorWriter.WriteLineAsync(message);
        } else {
          await dafnyOptions.OutputWriter.WriteLineAsync(message);
        }
      }

      projectFile.Validate(dafnyOptions.OutputWriter, AllOptions);
      dafnyOptions.DafnyProject = projectFile;
    } else {
      dafnyOptions.CliRootSourceUris.Add(new Uri(singleFile.FullName));
    }
    return true;
  }

  private static IEnumerable<Option> AllOptions {
    get {
      var result = new HashSet<Option>();
      var commands = new Stack<Command>();
      commands.Push(RootCommand);
      while (commands.Any()) {
        var current = commands.Pop();
        foreach (var option in current.Options) {
          result.Add(option);
        }
        foreach (var child in current.Subcommands) {
          commands.Push(child);
        }
      }
      return result;
    }
  }

  private static CommandLineBuilder AddDeveloperHelp(RootCommand rootCommand, CommandLineBuilder builder) {
    var languageDeveloperHelp = new Option<bool>(ToolchainDebuggingHelpName,
      "Show help and usage information, including options designed for developing the Dafny language and toolchain.");
    rootCommand.AddGlobalOption(languageDeveloperHelp);
    builder = builder.AddMiddleware(async (context, next) => {
      if (context.ParseResult.FindResultFor(languageDeveloperHelp) is { }) {
        context.InvocationResult = new HelpResult();
      } else {
        await next(context);
      }
    }, MiddlewareOrder.Configuration - 101);
    return builder;
  }

  public static ExitValue GetDafnyFiles(DafnyOptions options,
    out List<DafnyFile> dafnyFiles,
    out List<string> otherFiles) {
    dafnyFiles = new List<DafnyFile>();
    otherFiles = new List<string>();
    var outputWriter = options.OutputWriter;

    if (options.UseStdin) {
      var uri = new Uri("stdin:///");
      options.CliRootSourceUris.Add(uri);
      dafnyFiles.Add(new DafnyFile(options, uri));
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
        var df = new DafnyFile(options, new Uri(Path.GetFullPath(file)));
        if (options.LibraryFiles.Contains(file)) {
          df.IsPreverified = true;
          df.IsPrecompiled = true;
        }
        if (!filesSeen.Add(df.CanonicalPath)) {
          continue; // silently ignore duplicate
        }
        dafnyFiles.Add(df);
        isDafnyFile = true;
      } catch (ArgumentException e) {
        options.Printer.ErrorWriteLine(options.ErrorWriter, "*** Error: {0}: ", nameToShow, e.Message);
        return ExitValue.PREPROCESSING_ERROR;
      } catch (IllegalDafnyFile e) {
        if (e.ProcessingError) {
          return ExitValue.PREPROCESSING_ERROR;
        }
        // Fall through and try to handle the file as an "other file"
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

/// <summary>
/// The class HelpResult is internal to System.CommandLine so we have to include it as source.
/// It seems System.CommandLine didn't consider having more than one help option as a use-case.
/// </summary>
internal class HelpResult : IInvocationResult {
  public void Apply(InvocationContext context) {
    var output = context.Console.Out.CreateTextWriter();
    var helpBuilder = ((HelpBuilder)context.BindingContext.GetService(typeof(HelpBuilder)))!;
    var helpContext = new HelpContext(helpBuilder,
      context.ParseResult.CommandResult.Command,
      output,
      context.ParseResult);

    helpBuilder.Write(helpContext);
  }
}
