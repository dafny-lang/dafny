using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class CommandLineOption<T> : ICommandLineOption {
  public T Get(DafnyOptions options) {
    return Get(options.Options);
  }
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
  public virtual void PostProcess(DafnyOptions options) {
  }
}

public abstract class IntegerOption : CommandLineOption<int> {
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(IEnumerable<string> arguments) {

    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.First();
    if (int.TryParse(value, out var number)) {
      return new ParsedOption(arguments.Skip(1), number);
    }

    return new FailedOption($"Failed to parse value {value} as an integer for option {LongName}");
  }
}


public abstract class NaturalNumberOption : CommandLineOption<uint> {
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(IEnumerable<string> arguments) {
    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.First();
    if (uint.TryParse(value, out var number)) {
      return new ParsedOption(arguments.Skip(1), number);
    }

    return new FailedOption($"Failed to parse value {value} as a non-negative integer for option {LongName}");
  }
}

public abstract class BooleanOption : CommandLineOption<bool> {
  public override bool CanBeUsedMultipleTimes => false;
  public override object DefaultValue => false;

  public override ParseOptionResult Parse(IEnumerable<string> arguments) {
    var defaultResult = new ParsedOption(arguments, true);
    if (!arguments.Any()) {
      return defaultResult;
    }

    var value = arguments.First();
    return value switch {
      "0" => new ParsedOption(arguments.Skip(1), false),
      "1" => new ParsedOption(arguments.Skip(1), true),
      _ => defaultResult
    };
  }
}

abstract class StringOption : CommandLineOption<string> {
  public override ParseOptionResult Parse(IEnumerable<string> arguments) {
    var value = arguments.First();
    return new ParsedOption(arguments.Skip(1), value);
  }
}