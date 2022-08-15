using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

internal interface ParseArgumentResult {
}

record ParseArgumentSuccess(DafnyOptions DafnyOptions) : ParseArgumentResult;
record ParseArgumentFailure(string Message) : ParseArgumentResult;

static class CommandRegistry {
  private static readonly Dictionary<string, ICommand> Commands = new();

  public static string CommandOverview {
    get {
      var linePrefix = "\n  ";
      var commands = linePrefix + string.Join(linePrefix, Commands.Values.Select(command => command.Name.PadRight(18) + command.Description));
      var header = @"
Usage: dafny [dafny-options] [command] [command-options] [arguments]

Execute a Dafny command.

dafny-options:
  -h|--help         Show command line help.
  --version         Display Dafny version in use.

Dafny commands:";
      return header + commands;
    }
  }

  public static ISet<ICommandLineOption> CommonOptions = new HashSet<ICommandLineOption>(new ICommandLineOption[] {
    ShowSnippetsOption.Instance,
    CoresOption.Instance,
    VerificationTimeLimit.Instance,
    UseBaseFileName.Instance,
    PrintOption.Instance,
    HelpOption.Instance,
  });

  static void AddCommand(ICommand command) {
    Commands.Add(command.Name, command);
  }
  static CommandRegistry() {
    AddCommand(new BuildCommand());
    AddCommand(new VerifyCommand());
    AddCommand(new RunCommand());
  }

  class HelpOptions : DafnyOptions {
    public override string Help => CommandRegistry.CommandOverview;
  }

  [CanBeNull]
  public static ParseArgumentResult Create(string[] arguments) {
    // Special cases because we're still supporting the old style CLI as well.
    if (arguments[0] == "-h" || arguments[0] == "--help") {
      var helpOptions = new HelpOptions {
        HelpRequested = true
      };
      return new ParseArgumentSuccess(helpOptions);
    }
    if (arguments[0] == "--version") {
      var result = new DafnyOptions();
      result.VersionRequested = true;
      return new ParseArgumentSuccess(result);
    }

    if (!Commands.TryGetValue(arguments[0], out var command)) {
      return new ParseArgumentSuccess(DafnyOptions.Create(arguments));
    }

    var shortNames = command.Options.Where(o => o.ShortName != null).
      ToDictionary(o => o.ShortName, o => o);
    var longNames = command.Options.
      ToDictionary(o => o.LongName, o => o);
    var remainingArguments = arguments.Skip(1);
    var dafnyOptions = new CommandBasedOptions(command);
    var foundOptions = new HashSet<ICommandLineOption>();
    var optionValues = new Dictionary<ICommandLineOption, object>();
    var optionLessValues = new List<string>();
    var options = new Options(optionLessValues, optionValues);
    dafnyOptions.Options = options;
    while (remainingArguments.Any()) {
      var head = remainingArguments.First();
      remainingArguments = remainingArguments.Skip(1);
      var isLongName = head.StartsWith("--");
      var isShortName = head.StartsWith("-") && !isLongName;
      var equalsSplit = head.Split("=");
      if (equalsSplit.Length > 1) {
        remainingArguments = new[] { equalsSplit[1] }.Concat(remainingArguments);
        head = equalsSplit[0];
      }
      if (isLongName || isShortName) {
        ICommandLineOption option;
        string optionName;
        if (isLongName) {
          optionName = head.Substring(2);
          option = longNames.GetValueOrDefault(optionName);
        } else {
          optionName = head.Substring(1);
          option = shortNames.GetValueOrDefault(optionName);
        }
        if (option == null) {
          if (isLongName) {
            remainingArguments = dafnyOptions.RecogniseOldOptions(optionName, remainingArguments);
            if (remainingArguments == null) {
              var hint = "";
              if (optionName.Contains(":")) {
                hint += " Did you mean to use '=' instead of ':' ?";
              }
              return new ParseArgumentFailure($"There's no option named {optionName}." + hint);
            }
          } else {
            return new ParseArgumentFailure($"There's no option with the short name {optionName}.");
          }
        } else {
          foundOptions.Add(option);
          switch (option.Parse(dafnyOptions, remainingArguments)) {
            case FailedOption failedOption:
              return new ParseArgumentFailure(failedOption.Message);
            case ParsedOption parsedOption:
              if (option.CanBeUsedMultipleTimes) {
                var values = (List<object>)optionValues.GetOrCreate(option, () => new List<object>());
                values.Add(parsedOption.Value);
              } else {
                optionValues[option] = parsedOption.Value;
              }
              remainingArguments = remainingArguments.Skip(parsedOption.ConsumedArguments);
              break;
          }

        }

      } else {
        dafnyOptions.AddFile(head);
        optionLessValues.Add(head);
      }
    }
    foreach (var notFoundOption in command.Options.Except(foundOptions)) {
      optionValues[notFoundOption] = notFoundOption.GetDefaultValue(dafnyOptions);
    }
    foreach (var option in command.Options) {
      option.PostProcess(dafnyOptions);
    }

    command.PostProcess(dafnyOptions, options);
    dafnyOptions.ApplyDefaultOptions();
    return new ParseArgumentSuccess(dafnyOptions);
  }
}

class CommandBasedOptions : DafnyOptions {
  public ICommand Command { get; }

  private readonly ISet<string> obsoleteOptions = new HashSet<string>() {
    "spillTargetCode", "compile", "dafnyVerify"
  };

  public CommandBasedOptions(ICommand command) {
    this.Command = command;
  }

  public void AddFile(string file) {
    base.AddFile(file, null);
  }

  public override string Help {
    get {
      var boogieStep1 = new Regex(@"/(\w+):").Replace(BoogieHelpBody, "--boogie-$1=");
      var boogieStep2 = new Regex(@"/(\w+)").Replace(boogieStep1, "--boogie-$1");
      var step1 = new Regex(@"/(\w+):").Replace(HelpHeader + this.DafnyHelpBody,"--$1=");
      var step2 = new Regex(@"/(\w+)").Replace(step1, "--$1");
      return ICommandLineOption.GenerateHelp(step2 + boogieStep2, Command.Options);
    }
  }

  protected override bool ParseOption(string name, CommandLineParseState ps) {
    if (obsoleteOptions.Contains(name)) {
      ps.Error($"Option ${name} is not allowed when using a command.");
      return false;
    }
    return base.ParseOption(name, ps);
  }

  public IEnumerable<string> RecogniseOldOptions(string optionName, IEnumerable<string> remainingArguments) {
    var parseState = new CommandLineParseState(remainingArguments.ToArray(), "foo");
    parseState.s = "-" + optionName;
    const string boogiePrefix = "boogie-";
    if (optionName.StartsWith(boogiePrefix)) {
      optionName = optionName.Substring(boogiePrefix.Length);
      if (ParseBoogieOption(optionName, parseState)) {
        return remainingArguments.Skip(parseState.nextIndex);
      }
    } else {
      if (ParseDafnySpecificOption(optionName, parseState)) {
        return remainingArguments.Skip(parseState.nextIndex);
      }
    }

    return null;
  }
}