using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Help;
using System.CommandLine.Invocation;
using System.CommandLine.IO;
using System.CommandLine.Parsing;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Reflection;
using System.Threading.Tasks;
using DafnyCore;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Command = System.CommandLine.Command;

namespace Microsoft.Dafny;

class TelemetryPublisher : ITelemetryPublisher {
  private readonly ILogger<ITelemetryPublisher> logger;

  public TelemetryPublisher(ILogger<ITelemetryPublisher> logger) {
    this.logger = logger;
  }

  public void PublishTelemetry(ImmutableDictionary<string, object> data) {
    // TODO throw new NotImplementedException();
  }

  // TODO make ITelemetryPublisher abstract class and move this there.
  public void PublishUnhandledException(Exception e) {
    logger.LogError(e, "exception occurred");
    PublishTelemetry(ImmutableDictionary.Create<string, object>().
      Add("kind", ITelemetryPublisher.TelemetryEventKind.UnhandledException).
      Add("payload", e.ToString()));
  }
}

public class DafnyNewCli {
  private readonly DafnyOptions options;
  public const string ToolchainDebuggingHelpName = "--help-internal";
  public static readonly RootCommand RootCommand = new("The Dafny CLI enables working with Dafny, a verification-aware programming language. Use 'dafny -?' to see help for the previous CLI format.");

  private readonly CreateCompilation createCompilation;

  public DafnyNewCli(DafnyOptions options) {
    this.options = options;

    var fileSystem = OnDiskFileSystem.Instance;
    ILoggerFactory factory = new LoggerFactory();
    var telemetryPublisher = new TelemetryPublisher(factory.CreateLogger<ITelemetryPublisher>());
    createCompilation = (engine, input) => new Compilation(factory.CreateLogger<Compilation>(), fileSystem,
      new TextDocumentLoader(factory.CreateLogger<ITextDocumentLoader>(),
        new DafnyLangParser(this.options, fileSystem, telemetryPublisher,
          factory.CreateLogger<DafnyLangParser>(),
          factory.CreateLogger<CachingParser>()),
        new DafnyLangSymbolResolver(factory.CreateLogger<DafnyLangSymbolResolver>(),
          factory.CreateLogger<CachingResolver>(),
          telemetryPublisher)), new DafnyProgramVerifier(factory.CreateLogger<DafnyProgramVerifier>()),
      engine, input);
  }

  public async Task<int> RunCompilerWithCliAsUi() {

    options.RunningBoogieFromCommandLine = true;

    var input = new CompilationInput(options, 0, options.DafnyProject);
    var executionEngine = new ExecutionEngine(options, new VerificationResultCache(), DafnyMain.LargeThreadScheduler);
    var compilation = createCompilation(executionEngine, input);

    ConcurrentBag<IImplementationTask> tasksToVerify = new();
    var statSum = new PipelineStatistics();
    var er = new ConsoleErrorReporter(options);
    
    var consoleCollector = new ConcurrentToSequentialWriteManager(options.OutputWriter);
    var writerPerTok = new Dictionary<Boogie.IToken, TextWriter>();
          
    
    compilation.Updates.Subscribe(ev => {
      if (ev is NewDiagnostic newDiagnostic) {
        var dafnyDiagnostic = newDiagnostic.Diagnostic;
        er.Message(dafnyDiagnostic.Source, dafnyDiagnostic.Level,
          dafnyDiagnostic.ErrorId, dafnyDiagnostic.Token, dafnyDiagnostic.Message);
      }

      if (ev is CanVerifyPartsIdentified canVerifyPartsIdentified) {
        foreach (var part in canVerifyPartsIdentified.Parts) {
          tasksToVerify.Add(part);
        }
      }

      if (ev is BoogieUpdate boogieUpdate) {
        if (boogieUpdate.BoogieStatus is Completed completed) {
          var writer = writerPerTok[BoogieGenerator.ToDafnyToken(false, boogieUpdate.ImplementationTask.Implementation.tok)];
          
          var output = completed.Result.GetOutput(options.Printer, executionEngine, new PipelineStatistics(), _ => { });
          _ = writer.WriteAsync(output);
          writer.Dispose();
        }
        if (boogieUpdate.BoogieStatus is BatchCompleted batchCompleted) {
          switch (batchCompleted.VcResult.outcome) {
            case ProverInterface.Outcome.Valid:
            case ProverInterface.Outcome.Bounded:
              statSum.VerifiedCount += 1;
              break;
            case ProverInterface.Outcome.Invalid:
              statSum.ErrorCount += 1;
              break;
            case ProverInterface.Outcome.TimeOut:
              statSum.TimeoutCount += 1;
              break;
            case ProverInterface.Outcome.OutOfMemory:
              statSum.OutOfMemoryCount += 1;
              break;
            case ProverInterface.Outcome.OutOfResource:
              statSum.OutOfResourceCount += 1;
              break;
            case ProverInterface.Outcome.Undetermined:
              statSum.InconclusiveCount += 1;
              break;
            default:
              throw new ArgumentOutOfRangeException();
          }
        }
      }
    });
    compilation.Start();

    var resolution = await compilation.Resolution;
    var canVerifies = resolution.CanVerifies?.ToList();

    ConcurrentBag<IImplementationTask> completedTasks = new();
    var completedCanVerifyUpdates = compilation.Updates.
      Where(u => u is BoogieUpdate { BoogieStatus: Completed }).
      Do(u => {
        if (u is BoogieUpdate { BoogieStatus: Completed } boogieUpdate) {
          completedTasks.Add(boogieUpdate.ImplementationTask);
        }
      }).Select(_ => completedTasks.Count);

    if (canVerifies != null) {
      foreach (var canVerify in canVerifies.OrderBy(v => v.Tok.pos)) {
        writerPerTok[canVerify.Tok] = consoleCollector.AppendWriter();
        await compilation.VerifyCanVerify(canVerify, false);
      }
    }

    await completedCanVerifyUpdates.Where(i =>
      completedTasks.Count == tasksToVerify.Count).FirstAsync().ToTask();

    CompilerDriver.WriteTrailer(options, /* TODO ErrorWriter? */ options.OutputWriter, statSum);

    var exitValue = er.ErrorCount > 0 ? ExitValue.COMPILE_ERROR : ExitValue.SUCCESS;
    return (int)exitValue;
  }

  private static void AddCommand(Command command) {
    RootCommand.AddCommand(command);
  }

  static DafnyNewCli() {
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
      dafnyOptions.UsingNewCli = true;
      if (dafnyOptions.DafnyProject == null) {
        var uri = dafnyOptions.CliRootSourceUris.First();
        dafnyOptions.DafnyProject = new DafnyProject {
          Includes = Array.Empty<string>(),
          Uri = uri
        };
      }
      context.ExitCode = await continuation(dafnyOptions, context);
    }

    command.SetHandler(Handle);
  }

  public static async Task<int> Execute(TextWriter outputWriter,
    TextWriter errorWriter,
    TextReader inputReader, string[] arguments) {

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

    var console = new WritersConsole(inputReader, outputWriter, errorWriter);
    return await Parser.InvokeAsync(arguments, console);
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
}

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