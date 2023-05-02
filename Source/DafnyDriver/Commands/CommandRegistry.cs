using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Help;
using System.CommandLine.Invocation;
using System.CommandLine.IO;
using System.CommandLine.Parsing;
using System.IO;
using System.Linq;
using DafnyCore;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

internal interface ParseArgumentResult {
}

record ParseArgumentSuccess(DafnyOptions DafnyOptions) : ParseArgumentResult;
record ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult ExitResult) : ParseArgumentResult;

static class CommandRegistry {
  private const string ToolchainDebuggingHelpName = "--help-internal";
  private static readonly HashSet<ICommandSpec> Commands = new();

  static void AddCommand(ICommandSpec command) {
    Commands.Add(command);
  }

  static CommandRegistry() {
    AddCommand(new ResolveCommand());
    AddCommand(new VerifyCommand());
    AddCommand(new BuildCommand());
    AddCommand(new RunCommand());
    AddCommand(new TranslateCommand());
    AddCommand(new FormatCommand());
    AddCommand(new MeasureComplexityCommand());
    AddCommand(ServerCommand.Instance);
    AddCommand(new TestCommand());
    AddCommand(new GenerateTestsCommand());
    AddCommand(new DeadCodeCommand());
    AddCommand(new AuditCommand());

    // Check that the .doo file format is aware of all options,
    // and therefore which have to be saved to safely support separate verification/compilation.
    DooFile.CheckOptions(AllOptions);

    FileArgument = new Argument<FileInfo>("file", "Dafny input file or Dafny project file");
  }

  public static Argument<FileInfo> FileArgument { get; }

  [CanBeNull]
  public static ParseArgumentResult Create(string[] arguments) {
    bool allowHidden = arguments.All(a => a != ToolchainDebuggingHelpName);

    var wasInvoked = false;
    var dafnyOptions = new DafnyOptions();
    var optionValues = new Dictionary<Option, object>();
    var options = new Options(optionValues);
    dafnyOptions.ShowEnv = ExecutionEngineOptions.ShowEnvironment.Never;
    dafnyOptions.Environment = "Command-line arguments: " + string.Join(" ", arguments);
    dafnyOptions.Options = options;

    foreach (var option in AllOptions) {
      if (!allowHidden) {
        option.IsHidden = false;
      }
      if (!option.Arity.Equals(ArgumentArity.ZeroOrMore) && !option.Arity.Equals(ArgumentArity.OneOrMore)) {
        option.AllowMultipleArgumentsPerToken = true;
      }
    }

    var commandToSpec = Commands.ToDictionary(c => {
      var result = c.Create();
      foreach (var option in c.Options) {
        result.AddOption(option);
      }
      return result;
    }, c => c);
    foreach (var command in commandToSpec.Keys) {
      command.SetHandler(CommandHandler);
    }

    if (arguments.Length != 0) {
      var first = arguments[0];
      var keywordForNewMode = commandToSpec.Keys.Select(c => c.Name).
        Union(new[] { "--version", "-h", ToolchainDebuggingHelpName, "--help", "[parse]", "[suggest]" });
      if (!keywordForNewMode.Contains(first)) {
        if (first.Length > 0 && first[0] != '/' && first[0] != '-' && !File.Exists(first) && first.IndexOf('.') == -1) {
          dafnyOptions.Printer.ErrorWriteLine(Console.Out,
            "*** Error: '{0}': The first input must be a command or a legacy option or file with supported extension", first);
          return new ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR);
        }
        var oldOptions = new DafnyOptions();
        if (oldOptions.Parse(arguments)) {
          return new ParseArgumentSuccess(oldOptions);
        }

        return new ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR);
      }
    }
    dafnyOptions.UsingNewCli = true;

    var rootCommand = new RootCommand("The Dafny CLI enables working with Dafny, a verification-aware programming language. Use 'dafny /help' to see help for a previous CLI format.");
    foreach (var command in commandToSpec.Keys) {
      rootCommand.AddCommand(command);
    }

    var failedToProcessFile = false;
    void CommandHandler(InvocationContext context) {
      wasInvoked = true;
      var command = context.ParseResult.CommandResult.Command;
      var commandSpec = commandToSpec[command];

      var singleFile = context.ParseResult.GetValueForArgument(FileArgument);
      if (singleFile != null) {
        if (!ProcessFile(dafnyOptions, singleFile)) {
          failedToProcessFile = true;
          return;
        }
      }
      var files = context.ParseResult.GetValueForArgument(ICommandSpec.FilesArgument);
      if (files != null) {
        foreach (var file in files) {
          if (!ProcessFile(dafnyOptions, file)) {
            failedToProcessFile = true;
            return;
          }
        }
      }

      foreach (var option in command.Options) {
        var result = context.ParseResult.FindResultFor(option);
        object projectFileValue = null;
        var hasProjectFileValue = dafnyOptions.ProjectFile?.TryGetValue(option, Console.Error, out projectFileValue) ?? false;
        var value = result == null && hasProjectFileValue
          ? projectFileValue
          : context.ParseResult.GetValueForOption(option);
        options.OptionArguments[option] = value;
        dafnyOptions.ApplyBinding(option);
      }

      dafnyOptions.CurrentCommand = command;
      dafnyOptions.ApplyDefaultOptionsWithoutSettingsDefault();
      commandSpec.PostProcess(dafnyOptions, options, context);
    }

    var builder = new CommandLineBuilder(rootCommand).UseDefaults();
    builder = AddDeveloperHelp(rootCommand, builder);

#pragma warning disable VSTHRD002
    var exitCode = builder.Build().InvokeAsync(arguments).Result;
#pragma warning restore VSTHRD002

    if (failedToProcessFile) {
      return new ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR);
    }

    if (!wasInvoked) {
      if (exitCode == 0) {
        return new ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult.OK_EXIT_EARLY);
      }

      return new ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR);
    }
    if (exitCode == 0) {
      return new ParseArgumentSuccess(dafnyOptions);
    }

    return new ParseArgumentFailure(DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR);
  }

  private static bool ProcessFile(DafnyOptions dafnyOptions, FileInfo singleFile) {
    if (Path.GetExtension(singleFile.FullName) == ".toml") {
      if (dafnyOptions.ProjectFile != null) {
        Console.Error.WriteLine($"Only one project file can be used at a time. Both {dafnyOptions.ProjectFile.Uri.LocalPath} and {singleFile.FullName} were specified");
        return false;
      }

      if (!File.Exists(singleFile.FullName)) {
        Console.Error.WriteLine($"Error: file {singleFile.FullName} not found");
        return false;
      }
      var projectFile = ProjectFile.Open(new Uri(singleFile.FullName), Console.Error);
      if (projectFile == null) {
        return false;
      }
      projectFile.Validate(AllOptions);
      dafnyOptions.ProjectFile = projectFile;
      projectFile.AddFilesToOptions(dafnyOptions);
    } else {
      dafnyOptions.AddFile(singleFile.FullName);
    }
    return true;
  }

  private static IEnumerable<Option> AllOptions {
    get { return Commands.SelectMany(c => c.Options); }
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
