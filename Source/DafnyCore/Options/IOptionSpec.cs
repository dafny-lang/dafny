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
  string Description { get; }
  void Parse(CommandLineParseState ps, DafnyOptions options);

  string PostProcess(DafnyOptions options);
}

public abstract class CommandLineOption<T> : IOptionSpec {
  public T Get(DafnyOptions options) {
    return Get(options.Options);
  }

  protected void InvalidArgumentError(string name, Boogie.CommandLineParseState ps) {
    ps.Error($"Invalid argument to option {name}: {ps.args[ps.i]}");
  }

  public T Get(Options options) {
    if (options.OptionArguments.TryGetValue(this, out var result)) {
      return (T)result;
    }

    return default;
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
      if (DefaultValue != null) {
        result.SetDefaultValue(DefaultValue);
      }
      result.IsHidden = Hidden;
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
    int result = 0;
    if (ps.GetIntArgument(ref result, 2)) {
      Set(options, result == 1);
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
