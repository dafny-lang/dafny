using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.CommandLine;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public interface IOptionSpec {

  bool Hidden { get; }
  Option ToOption { get; }
  object DefaultValue { get; }
  string LongName { get; }
  string ShortName { get; }
  string ArgumentName { get; }
  string Category { get; }
  string Description { get; }
  void Parse(CommandLineParseState ps, DafnyOptions options);

  string PostProcess(DafnyOptions options);

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

  protected void InvalidArgumentError(string name, Boogie.CommandLineParseState ps) {
    ps.Error("Invalid argument \"{0}\" to option {1}", ps.args[ps.i], name);
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

  public virtual bool Hidden => false;

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
  public virtual string ShortName => null;
  public abstract string ArgumentName { get; }
  public abstract string Category { get; }
  public abstract string Description { get; }
  public abstract void Parse(CommandLineParseState ps, DafnyOptions options);

  public abstract string PostProcess(DafnyOptions options);
}

public abstract class IntegerOption : CommandLineOption<int> {
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    int a = 0;
    if (ps.GetIntArgument(ref a)) {
      Set(options, a);
      options.ArithMode = a;
    }
  }
}

public abstract class NaturalNumberOption : CommandLineOption<uint> {
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    uint a = 0;
    if (ps.GetUnsignedNumericArgument(ref a, _ => true)) {
      Set(options, a);
    }
  }
}

public abstract class BooleanOption : CommandLineOption<bool> {
  public override object DefaultValue => false;

  public override string ArgumentName => null;

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    int printEffects = 0;
    if (ps.GetIntArgument(ref printEffects, 2)) {
      Set(options, printEffects == 1);
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

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    if (ps.ConfirmArgumentCount(1)) {
      Set(options, ps.args[ps.i]);
    }
  }
}

public interface ParseOptionResult { }

public record ParsedOption(object Value) : ParseOptionResult;

public record FailedOption(string Message) : ParseOptionResult;
