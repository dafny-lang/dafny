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