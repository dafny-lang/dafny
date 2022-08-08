using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;


abstract class CommandLineOption<T> : ICommandLineOption {
  public T Get(Options options) {
    return (T)options.OptionArguments[LongName];
  }
  public void Set(Options options, T value) {
    options.OptionArguments[LongName] = value;
  }

  public abstract object DefaultValue { get; }
  public abstract string LongName { get; }
  public abstract string ShortName { get; }
  public abstract string Description { get; }
  public abstract bool CanBeUsedMultipleTimes { get; }
  public abstract ParseOptionResult Parse(IEnumerable<string> arguments);
}

abstract class IntegerOption : CommandLineOption<int> {
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(IEnumerable<string> arguments) {

    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.First();
    if (int.TryParse(value, out var number)) {
      return new ParsedOption(arguments.Skip(1), number);
    }
    return value switch {
      "0" => new ParsedOption(arguments.Skip(1), false),
      "1" => new ParsedOption(arguments.Skip(1), true),
      _ => new FailedOption("blerp")
    };
  }
}

abstract class BooleanOption : CommandLineOption<bool> {
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(IEnumerable<string> arguments) {
    if (!arguments.Any()) {
      return new ParsedOption(arguments, true);
    }

    var value = arguments.First();
    return value switch {
      "0" => new ParsedOption(arguments.Skip(1), false),
      "1" => new ParsedOption(arguments.Skip(1), true),
      _ => new FailedOption("blerp")
    };
  }
}

class ShowSnippetsOption : BooleanOption {
  public static readonly ShowSnippetsOption Instance = new();

  public override object DefaultValue => false;
  public override string LongName => "showSnippets";
  public override string ShortName => null;

  public override string Description => @"
/showSnippets:<n>
    0 (default) - don't show source code snippets for Dafny messages
    1 - show a source code snippet for each Dafny message".TrimStart();
}

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override object DefaultValue => false;
  public override string LongName => "noVerify";
  public override string ShortName => null;
  public override string Description => "missing";
}