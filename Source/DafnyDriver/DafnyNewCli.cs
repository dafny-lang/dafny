#nullable enable
using System;
using System.Collections;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Invocation;
using System.CommandLine.Parsing;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.LanguageServer;

namespace Microsoft.Dafny;

public static class DafnyNewCli {
  public const string ToolchainDebuggingHelpName = "--help-internal";
  public static readonly RootCommand RootCommand = new("The Dafny CLI enables working with Dafny, a verification-aware programming language. Use 'dafny -?' to see help for the previous CLI format.");

  private static void AddCommand(Command command) {
    RootCommand.AddCommand(command);
    RootCommand.TreatUnmatchedTokensAsErrors = false;
  }

  static DafnyNewCli() {
    DafnyFile.RegisterExtensionHandler(DafnyProject.Extension, (options, fileSystem, reporter, uri, uriOrigin, asLibrary) => HandleDafnyProject(fileSystem, options, reporter, uri, uriOrigin, asLibrary));
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
    AddCommand(DocumentationCommand.Create());
    AddCommand(ExtractCommand.Create());

    OptionRegistry.CheckOptionsAreKnown(AllOptions);

    // This SHOULD find the same method but returns null for some reason:
    // typeof(ParseResult).GetMethod("GetValueForOption", 1, new[] { typeof(Option<>) });
    foreach (var method in typeof(ParseResult).GetMethods()) {
      if (method.Name == "GetValueForOption" && method.GetGenericArguments().Length == 1) {
        GetValueForOptionMethod = method;
      }
    }
    Debug.Assert(GetValueForOptionMethod != null);

    var builder = new CommandLineBuilder(RootCommand).UseDefaults();
    builder = AddDeveloperHelp(RootCommand, builder);
    Parser = builder.Build();
  }

  public delegate Task<int> ContinueWithOptions(DafnyOptions dafnyOptions, InvocationContext context);
  public static void SetHandlerUsingDafnyOptionsContinuation(Command command, ContinueWithOptions continuation) {

    async Task Handle(InvocationContext context) {
      WritersConsole console = (WritersConsole)context.Console;
      var dafnyOptions = new DafnyOptions(console.InputWriter, console.OutWriter, console.ErrWriter);
      dafnyOptions.Environment =
        "Command-line arguments: " + string.Join(" ", context.ParseResult.Tokens.Select(t => t.Value).
          Where(s => !string.IsNullOrEmpty(s)));
      dafnyOptions.ShowEnv = ExecutionEngineOptions.ShowEnvironment.Never;
      var optionValues = new Dictionary<Option, object>();
      var options = new Options(optionValues, new Dictionary<Argument, object>());
      dafnyOptions.Options = options;

      foreach (var argument in command.Arguments) {
        var result = context.ParseResult.FindResultFor(argument)?.GetValueOrDefault();
        if (result != null) {
          options.Arguments[argument] = result;
        }
      }

      ProcessOption(context, CommonOptionBag.UseBaseFileName, dafnyOptions);
      dafnyOptions.ApplyBinding(CommonOptionBag.UseBaseFileName);

      var singleFile = context.ParseResult.GetValueForArgument(DafnyCommands.FileArgument);
      if (singleFile != null) {
        if (!await ProcessFile(dafnyOptions, singleFile)) {
          context.ExitCode = (int)ExitValue.PREPROCESSING_ERROR;
          return;
        }
      }
      var files = context.ParseResult.GetValueForArgument(DafnyCommands.FilesArgument);
      if (files != null) {
        foreach (var file in files) {
          if (!await ProcessFile(dafnyOptions, file)) {
            context.ExitCode = (int)ExitValue.PREPROCESSING_ERROR;
            return;
          }
        }
      }

      ProcessOption(context, DafnyProject.FindProjectOption, dafnyOptions);
      var firstFile = dafnyOptions.CliRootSourceUris.FirstOrDefault();
      if (dafnyOptions.DafnyProject == null && dafnyOptions.Get(DafnyProject.FindProjectOption) && firstFile != null) {
        var opener = new ProjectFileOpener(OnDiskFileSystem.Instance, Token.Cli);
        var project = await opener.TryFindProject(firstFile);
        project?.Validate(dafnyOptions.OutputWriter, AllOptions);
        dafnyOptions.DafnyProject = project;
      }

      foreach (var option in command.Options) {
        if (option == CommonOptionBag.UseBaseFileName || option == DafnyProject.FindProjectOption) {
          continue;
        }
        ProcessOption(context, option, dafnyOptions);
      }

      foreach (var option in command.Options) {
        try {
          dafnyOptions.ApplyBinding(option);
        } catch (Exception e) {
          context.ExitCode = (int)ExitValue.PREPROCESSING_ERROR;
          await dafnyOptions.OutputWriter.WriteLineAsync(
            $"Invalid value for option {option.Name}: {e.Message}");
          return;
        }
      }

      dafnyOptions.ApplyDefaultOptionsWithoutSettingsDefault();
      dafnyOptions.UsingNewCli = true;

      if (dafnyOptions.Get(CommonOptionBag.WaitForDebugger)) {
        while (!Debugger.IsAttached) {
          Thread.Sleep(100);
        }
      }

      context.ExitCode = await continuation(dafnyOptions, context);
    }

    command.SetHandler(Handle);
  }

  private static void ProcessOption(InvocationContext context, Option option, DafnyOptions dafnyOptions) {
    var options = dafnyOptions.Options;
    var result = context.ParseResult.FindResultFor(option);
    object? projectFileValue = null;
    var hasProjectFileValue = dafnyOptions.DafnyProject?.TryGetValue(option, out projectFileValue) ?? false;
    object value;
    if (option.Arity.MaximumNumberOfValues <= 1) {
      // If multiple values aren't allowed, CLI options take precedence over project file options
      value = (result == null || Equals(result.Token, null)) && hasProjectFileValue
        ? projectFileValue!
        : GetValueForOption(context.ParseResult, option);
    } else {
      // If multiple values ARE allowed, CLI options come after project file options
      var elementType = option.ValueType.GetGenericArguments()[0];
      var valueAsList = (IList)Activator.CreateInstance(typeof(List<>).MakeGenericType(elementType))!;
      if (hasProjectFileValue) {
        foreach (var element in (IEnumerable)projectFileValue!) {
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
  }

  public static Task<int> Execute(IConsole console, IReadOnlyList<string> arguments) {
    foreach (var symbol in AllSymbols) {
      if (symbol is Option option) {
        if (!option.Arity.Equals(ArgumentArity.ZeroOrMore) && !option.Arity.Equals(ArgumentArity.OneOrMore)) {
          option.AllowMultipleArgumentsPerToken = true;
        }
      }
    }

    return Parser.InvokeAsync(arguments.ToArray(), console);
  }

  private static readonly MethodInfo GetValueForOptionMethod;
  private static readonly System.CommandLine.Parsing.Parser Parser;

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
    return generic.Invoke(result, [option])!;
  }

  private static async Task<bool> ProcessFile(DafnyOptions dafnyOptions, FileInfo singleFile) {
    var isProjectFile = Path.GetExtension(singleFile.FullName) == DafnyProject.Extension;
    if (isProjectFile) {
      return await ProcessProjectFile(dafnyOptions, new Uri(singleFile.FullName));
    }

    dafnyOptions.CliRootSourceUris.Add(new Uri(singleFile.FullName));
    return true;
  }

  private static async Task<bool> ProcessProjectFile(DafnyOptions dafnyOptions, Uri file) {
    if (dafnyOptions.DafnyProject != null) {
      var first = dafnyOptions.GetPrintPath(dafnyOptions.DafnyProject.Uri.LocalPath);
      await dafnyOptions.ErrorWriter.WriteLineAsync($"Only one project file can be used at a time. Both {first} and {dafnyOptions.GetPrintPath(file.LocalPath)} were specified");
      return false;
    }

    if (!File.Exists(file.LocalPath)) {
      await dafnyOptions.ErrorWriter.WriteLineAsync($"Error: file {dafnyOptions.GetPrintPath(file.LocalPath)} not found");
      return false;
    }
    var projectFile = await DafnyProject.Open(OnDiskFileSystem.Instance, file, Token.Cli);

    projectFile.Validate(dafnyOptions.OutputWriter, AllOptions);
    dafnyOptions.DafnyProject = projectFile;
    return true;
  }

  private static IEnumerable<IdentifierSymbol> AllSymbols {
    get {
      var result = new HashSet<IdentifierSymbol>();
      var commands = new Stack<Command>();
      commands.Push(RootCommand);
      while (commands.Any()) {
        var current = commands.Pop();
        result.Add(current);
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

  private static IEnumerable<Option> AllOptions => AllSymbols.OfType<Option>();

  private static CommandLineBuilder AddDeveloperHelp(RootCommand rootCommand, CommandLineBuilder builder) {
    var languageDeveloperHelp = new Option<bool>(ToolchainDebuggingHelpName,
      "Show help and usage information, including options designed for developing the Dafny language and toolchain.");
    rootCommand.AddGlobalOption(languageDeveloperHelp);
    bool helpShown = false;
    builder = builder.UseHelp(_ => helpShown = true);

    builder = builder.AddMiddleware(async (context, next) => {
      if ((context.ParseResult.CommandResult.Command.IsHidden && helpShown) || context.ParseResult.FindResultFor(languageDeveloperHelp) is { }) {

        foreach (var symbol in AllSymbols) {
          symbol.IsHidden = false;
        }

        context.InvocationResult = new HelpResult();
      } else {
        await next(context);
      }
    }, MiddlewareOrder.Configuration - 101);
    return builder;
  }

  private static async IAsyncEnumerable<DafnyFile> HandleDafnyProject(IFileSystem fileSystem, DafnyOptions options,
    ErrorReporter reporter,
    Uri uri,
    IOrigin uriOrigin,
    bool asLibrary) {
    if (!asLibrary) {
      reporter.Error(MessageSource.Project, uriOrigin, "Using a Dafny project file as a source file is not supported.");
      yield break;
    }

    var dependencyProject = await DafnyProject.Open(fileSystem, uri, uriOrigin);
    var dependencyOptions =
      DooFile.CheckAndGetLibraryOptions(reporter, uri, options, uriOrigin, dependencyProject.Options);
    if (dependencyOptions == null) {
      yield break;
    }

    if (options.Get(DafnyFile.DoNotVerifyDependencies) || !options.Verify) {
      foreach (var libraryRootSetFile in dependencyProject.GetRootSourceUris(fileSystem)) {
        var file = DafnyFile.HandleDafnyFile(fileSystem, reporter, dependencyOptions, libraryRootSetFile,
          dependencyProject.StartingToken, true, false);
        if (file != null) {
          yield return file;
        }
      }
    } else {
      if (options.Verbose) {
        await options.OutputWriter.WriteLineAsync($"Building dependency {options.GetPrintPath(uri.LocalPath)}");
      }

      dependencyOptions.Compile = true;
      dependencyOptions.RunAfterCompile = false;
      var libraryBackend = new LibraryBackend(dependencyOptions);
      dependencyOptions.Backend = libraryBackend;
      dependencyOptions.CompilerName = dependencyOptions.Backend.TargetId;

      dependencyOptions.DafnyProject = dependencyProject;
      dependencyOptions.CliRootSourceUris.Clear();
      dependencyOptions.Compile = true;
      dependencyOptions.RunAfterCompile = false;
      var exitCode = await SynchronousCliCompilation.Run(dependencyOptions);
      if (exitCode == 0 && libraryBackend.DooPath != null) {
        var dooUri = new Uri(libraryBackend.DooPath);
        await foreach (var dooResult in DafnyFile.HandleDooFile(fileSystem, reporter, options, dooUri, uriOrigin, true)) {
          yield return dooResult;
        }
      } else {
        reporter.Error(MessageSource.Project, uriOrigin, $"Failed to build dependency {options.GetPrintPath(uri.LocalPath)}");
      }
    }

  }
}