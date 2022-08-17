using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.CommandLine;

namespace Microsoft.Dafny;

public interface IOptionSpec {

  Option ToOption { get; }
  object DefaultValue { get; }
  string LongName { get; }
  string ShortName { get; }
  string ArgumentName { get; }
  string Category { get; }
  string Description { get; }
  ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments);
  string PostProcess(DafnyOptions options, object value);

  public static string GenerateHelp(string template, IEnumerable<IOptionSpec> options, bool oldStyle = false) {
    var regex = new Regex(@"----\s([^-]+)\s-+(?:\r\n|\r|\n)\ *(?:\r\n|\r|\n)");
    var categories = regex.Matches(template).ToArray();

    var optionsByCategory = options.GroupBy(option => option.Category).
      ToDictionary(g => g.Key, g => g as IEnumerable<IOptionSpec>);

    var output = new StringBuilder();
    var outputIndex = 0;
    for (var index = 0; index < categories.ToArray().Length; index++) {
      var category = categories.ToArray()[index];
      var preCategory = template.Substring(outputIndex, category.Index - outputIndex);
      output.Append(preCategory);
      outputIndex = category.Index + category.Length;
      var categoryName = category.Groups[1].Value;
      output.Append(category.Value);
      var optionsForCategory = optionsByCategory.GetValueOrDefault(categoryName, Enumerable.Empty<IOptionSpec>());

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

public abstract class CommandLineOption<T> : IOptionSpec {
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

  public virtual Option ToOption {
    get {
      var result = new Option<T>("--" + LongName, Description);
      result.SetDefaultValue(DefaultValue);
      result.ArgumentHelpName = ArgumentName;
      if (ShortName != null) {
        result.AddAlias("-" + ShortName);
      }
      return result;
    }
  }

  public abstract object DefaultValue { get; }
  public abstract string LongName { get; }
  public abstract string ShortName { get; }
  public abstract string ArgumentName { get; }
  public abstract string Category { get; }
  public abstract string Description { get; }
  public abstract ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments);

  public virtual string TypedPostProcess(DafnyOptions options, T value) {
    return null;
  }

  public string PostProcess(DafnyOptions options, object value) {
    return TypedPostProcess(options, (T)value);
  }
}

public abstract class IntegerOption : CommandLineOption<int> {

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments) {
    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.Pop();
    if (int.TryParse(value, out var number)) {
      return new ParsedOption(number);
    }

    return new FailedOption($"Failed to parse value {value} as an integer for option {LongName}");
  }
}

public abstract class NaturalNumberOption : CommandLineOption<uint> {

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments) {
    if (!arguments.Any()) {
      return new FailedOption($"No argument found for option {LongName}");
    }

    var value = arguments.Pop();
    if (uint.TryParse(value, out var number)) {
      return new ParsedOption(number);
    }

    return new FailedOption($"Failed to parse value {value} as a non-negative integer for option {LongName}");
  }
}

public abstract class BooleanOption : CommandLineOption<bool> {
  public override object DefaultValue => false;

  public override string ArgumentName => null;

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments) {
    var defaultResult = new ParsedOption(true);
    if (!arguments.Any()) {
      return defaultResult;
    }

    var value = arguments.Pop();
    switch (value) {
      case "0":
        return new ParsedOption(false);
      case "1":
        return new ParsedOption(true);
      default:
        arguments.Push(value);
        return defaultResult;
    }
  }
}

public abstract class StringOption : CommandLineOption<string> {
  protected virtual string[] AllowedValues => null;

  public override Option ToOption {
    get {
      var result = base.ToOption;
      if (AllowedValues != null) {
        result.FromAmong(AllowedValues);
      }

      return result;
    }
  }

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments) {
    var value = arguments.Pop();
    return new ParsedOption(value);
  }
}

public interface ParseOptionResult { }

public record ParsedOption(object Value) : ParseOptionResult;

public record FailedOption(string Message) : ParseOptionResult;
