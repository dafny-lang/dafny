using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

static class CommandRegistry {
  private static readonly Dictionary<string, ICommand> Commands = new();

  static void AddCommand(ICommand command) {
    Commands.Add(command.Name, command);
  }
  static CommandRegistry() {
    AddCommand(new BuildCommand());
    AddCommand(new VerifyCommand());
    AddCommand(new RunCommand());
  }

  [CanBeNull]
  public static DafnyOptions Create(string[] arguments) {
    if (Commands.TryGetValue(arguments[0], out var command)) {
      var result = new CommandBasedOptions(command);
      result.Parse(arguments.Skip(1).ToArray());
      command.PostProcess(result);
      return result;
    } else {
      var result = new DafnyOptions();
      result.Parse(arguments);
      return result;
    }
  }

  class CommandBasedOptions : DafnyOptions {
    private readonly ICommand command;

    public CommandBasedOptions(ICommand command) {
      this.command = command;
    }

    protected override bool ParseOption(string name, CommandLineParseState ps) {
      if (command.OverridenOptions.Contains(name)) {
        ps.Error($"Option {name} is not available for command {command.Name}.");
        return true;
      }
      return base.ParseOption(name, ps);
    }
  }
}
public interface ICommand {
  string Name { get; }

  string Help { get; }

  ISet<string> OverridenOptions { get; }

  void PostProcess(DafnyOptions options);
}

class BuildCommand : ICommand {
  public string Name => "build";
  public string Help => "Generate source file in the target language";

  public ISet<string> OverridenOptions => new HashSet<string> { "compile", "spillTargetLanguage" };
  public void PostProcess(DafnyOptions options) {
    options.Compile = false;
    options.RunAfterCompile = false;
    options.SpillTargetCode = options.Verify ? 4 : 2;
  }
}

class RunCommand : ICommand {
  public string Name => "run";
  public string Help => "Run the program";

  public ISet<string> OverridenOptions => new HashSet<string>() { "compile", "spillTargetLanguage" };
  public void PostProcess(DafnyOptions options) {
    options.Compile = true; // TODO can we prevent emitting executable artifacts?
    options.RunAfterCompile = true;
    if (!options.Verify) {
      options.ForceCompile = true;
    }
  }
}

class VerifyCommand : ICommand {
  public string Name => "verify";
  public string Help => "Verify the program";

  public ISet<string> OverridenOptions => new HashSet<string>() { "noVerify", "compile", "spillTargetLanguage" };
  public void PostProcess(DafnyOptions options) {
    options.Compile = false;
  }
}