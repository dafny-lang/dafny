using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

public interface ICommandLineOption {
  object GetDefaultValue(DafnyOptions options);
  string LongName { get; }

  string ShortName { get; }
  string Category { get; }
  string Description { get; }
  bool CanBeUsedMultipleTimes { get; }
  ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments);
  void PostProcess(DafnyOptions options);

  public static string GenerateHelp(string template, IEnumerable<ICommandLineOption> options, bool oldStyle = false) {
    var regex = new Regex(@"----\s([^-]+)\s-+(?:\r\n|\r|\n)\ *(?:\r\n|\r|\n)");
    var categories = regex.Matches(template).ToArray();

    var optionsByCategory = options.GroupBy(option => option.Category).
      ToDictionary(g => g.Key, g => g as IEnumerable<ICommandLineOption>);

    var output = new StringBuilder();
    var outputIndex = 0;
    for (var index = 0; index < categories.ToArray().Length; index++) {
      var category = categories.ToArray()[index];
      var preCategory = template.Substring(outputIndex, category.Index - outputIndex);
      output.Append(preCategory);
      outputIndex = category.Index + category.Length;
      var categoryName = category.Groups[1].Value;
      output.Append(category.Value);
      var optionsForCategory = optionsByCategory.GetValueOrDefault(categoryName, Enumerable.Empty<ICommandLineOption>());

      foreach (var option in optionsForCategory.OrderBy(o => o.LongName)) {
        var prefix = oldStyle ? "/" : "--";
        var suffix = oldStyle ? ":" : "=";
        var optionHelpHeader = "  " + prefix + option.LongName + suffix + "<value>";
        var linePrefix = "\n      ";
        var optionHelp = optionHelpHeader + linePrefix + string.Join(linePrefix, option.Description.Split("\n")) + "\n";
        output.Append(optionHelp);
      }
    }
    output.Append(template.Substring(outputIndex));

    return output.ToString();
  }
}

public abstract class CommandLineOption<T> : ICommandLineOption {
  public T Get(DafnyOptions options) {
    return Get(options.Options);
  }

  public T Get(Options options) {
    return (T)options.OptionArguments[this];
  }

  public void Set(DafnyOptions options, T value) {
    Set(options.Options, value);
  }
  public void Set(Options options, T value) {
    options.OptionArguments[this] = value;
  }

  public abstract object GetDefaultValue(DafnyOptions options);
  public abstract string LongName { get; }
  public abstract string ShortName { get; }
  public abstract string Category { get; }
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