using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public interface ICommandLineOption {
  object GetDefaultValue(DafnyOptions options);
  string LongName { get; }
  string ShortName { get; }
  string Description { get; }
  bool CanBeUsedMultipleTimes { get; }
  ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments);
  void PostProcess(DafnyOptions options);
}

public abstract class CommandLineOption<T> : ICommandLineOption {
  public T Get(DafnyOptions options) {
    return Get(options.Options);
  }

  public T Get(Options options) {
    return (T)options.OptionArguments[LongName];
  }

  public void Set(DafnyOptions options, T value) {
    Set(options.Options, value);
  }
  public void Set(Options options, T value) {
    options.OptionArguments[LongName] = value;
  }

  public abstract object GetDefaultValue(DafnyOptions options);
  public abstract string LongName { get; }
  public abstract string ShortName { get; }
  public abstract string Description { get; }
  public abstract bool CanBeUsedMultipleTimes { get; }
  public abstract ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments);

  public virtual void PostProcess(DafnyOptions options) {
  }
}

public abstract class IntegerOption : CommandLineOption<int> {
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments) {
    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.First();
    if (int.TryParse(value, out var number)) {
      return new ParsedOption(1, number);
    }

    return new FailedOption($"Failed to parse value {value} as an integer for option {LongName}");
  }
}

public abstract class NaturalNumberOption : CommandLineOption<uint> {
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments) {
    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.First();
    if (uint.TryParse(value, out var number)) {
      return new ParsedOption(1, number);
    }

    return new FailedOption($"Failed to parse value {value} as a non-negative integer for option {LongName}");
  }
}

public abstract class BooleanOption : CommandLineOption<bool> {
  public override bool CanBeUsedMultipleTimes => false;
  public override object GetDefaultValue(DafnyOptions options) => false;

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments) {
    var defaultResult = new ParsedOption(0, true);
    if (!arguments.Any()) {
      return defaultResult;
    }

    var value = arguments.First();
    return value switch {
      "0" => new ParsedOption(1, false),
      "1" => new ParsedOption(1, true),
      _ => defaultResult
    };
  }
}

public abstract class StringOption : CommandLineOption<string> {
  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments) {
    var value = arguments.First();
    return new ParsedOption(1, value);
  }
}

public interface ParseOptionResult { }

public record ParsedOption(int ConsumedArguments, object Value) : ParseOptionResult;

public record FailedOption(string Message) : ParseOptionResult;