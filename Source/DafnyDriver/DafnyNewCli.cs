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
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore;
using DafnyDriver.Commands;
using Microsoft.Boogie;
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
    DafnyFile.RegisterExtensionHandler(DafnyProject.Extension, HandleDafnyProject);
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

    // Check that the .doo file format is aware of all options,
    // and therefore which have to be saved to safely support separate verification/compilation.
    DooFile.CheckOptions(AllOptions);

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
      foreach (var option in command.Options) {
        if (option == CommonOptionBag.UseBaseFileName) {
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

  public static Task<int> Execute(IConsole console, string[] arguments) {
    bool allowHidden = arguments.All(a => a != ToolchainDebuggingHelpName);
    foreach (var symbol in AllSymbols) {
      if (!allowHidden) {
        symbol.IsHidden = false;
      }

      if (symbol is Option option) {
        if (!option.Arity.Equals(ArgumentArity.ZeroOrMore) && !option.Arity.Equals(ArgumentArity.OneOrMore)) {
          option.AllowMultipleArgumentsPerToken = true;
        }
      }
    }

    return Parser.InvokeAsync(arguments, console);
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
    return generic.Invoke(result, new object[] { option })!;
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
    var projectFile = await DafnyProject.Open(OnDiskFileSystem.Instance, dafnyOptions, file);

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
    builder = builder.AddMiddleware(async (context, next) => {
      if (context.ParseResult.FindResultFor(languageDeveloperHelp) is { }) {
        context.InvocationResult = new HelpResult();
      } else {
        await next(context);
      }
    }, MiddlewareOrder.Configuration - 101);
    return builder;
  }

  private static async Task<DafnyFile?> HandleDafnyProject(DafnyOptions options,
    IFileSystem fileSystem, ErrorReporter reporter,
    Uri uri,
    IToken origin,
    bool asLibrary) {
    if (!asLibrary) {
      reporter.Error(MessageSource.Project, origin, "Using a Dafny project file as a source file is not supported.");
      return null;
    }

    var outputWriter = new StringWriter();
    var errorWriter = new StringWriter();
    var exitCode = await DafnyNewCli.Execute(new WritersConsole(TextReader.Null, outputWriter, errorWriter),
      new[] { "build", "-t=lib", uri.LocalPath, "--verbose" });
    if (exitCode != 0) {
      var output = outputWriter + errorWriter.ToString();
      reporter.Error(MessageSource.Project, origin,
        $"Could not build a Dafny library from {uri.LocalPath} because:\n{output}");
      return null;
    }

    var regex = new Regex($"Wrote Dafny library to (.*)\n");
    var path = regex.Match(outputWriter.ToString());
    var dooUri = new Uri(path.Groups[1].Value);
    return await DafnyFile.HandleDooFile(options, fileSystem, reporter, dooUri, origin, true);
  }
}