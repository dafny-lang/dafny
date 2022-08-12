using System;
using System.Collections.Generic;
using System.Linq;
using Dafny;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

class NoVerifyOption : BooleanOption {
  public static readonly NoVerifyOption Instance = new();
  public override string LongName => "noVerify";
  public override string ShortName => null;
  public override string Description => "missing";

  public override void PostProcess(DafnyOptions options) {
    options.Verify = !Get(options);
    base.PostProcess(options);
  }
}

class PrintOption : StringOption {
  public static readonly PrintOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "print";
  public override string ShortName => null;
  public override string Description => "missing";
  public override bool CanBeUsedMultipleTimes => false;

  public override void PostProcess(DafnyOptions options) {
    options.DafnyPrintFile = Get(options);
    base.PostProcess(options);
  }
}

class TargetOption : StringOption {
  public static readonly TargetOption Instance = new();
  public override object DefaultValue => "cs";
  public override string LongName => "target";
  public override string ShortName => null;
  public override string Description => "missing";
  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(IEnumerable<string> arguments) {
    var target = arguments.First();
    var compilers = DafnyOptions.DefaultPlugins.SelectMany(p => p.GetCompilers()).ToList();
    var compiler = compilers.LastOrDefault(c => c.TargetId == target);
    if (compiler == null) {
      var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetLanguage})"));
      return new FailedOption($"No compiler found for compileTarget \"{target}\"; expecting one of {known}");
    }

    return new ParsedOption(1, target);
  }

  public override void PostProcess(DafnyOptions options) {
    var target = Get(options);
    var compilers = options.Plugins.SelectMany(p => p.GetCompilers()).ToList();
    options.Compiler = compilers.LastOrDefault(c => c.TargetId == target);
    base.PostProcess(options);
  }
}