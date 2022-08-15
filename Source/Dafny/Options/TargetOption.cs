using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

class CompileTargetOption : TargetOption {
  public new static readonly CompileTargetOption Instance = new();
  public override string LongName => "compileTarget";
}

public class TargetOption : CommandLineOption<Compiler> {
  public static readonly TargetOption Instance = new();
  public override object GetDefaultValue(DafnyOptions options) =>
    options.Plugins.SelectMany(p => p.GetCompilers()).First(c => c.TargetId == "cs");

  public override string LongName => "target";
  public override string ShortName => "t";
  public override string Category => "Compilation options";

  public override string Description => @"
cs (default) - Compilation to .NET via C#
go - Compilation to Go
js - Compilation to JavaScript
java - Compilation to Java
py - Compilation to Python
cpp - Compilation to C++

Note that the C++ backend has various limitations (see Docs/Compilation/Cpp.md).
This includes lack of support for BigIntegers (aka int), most higher order
functions, and advanced features like traits or co-inductive types.".TrimStart();

  public override bool CanBeUsedMultipleTimes => false;

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, IEnumerable<string> arguments) {
    var target = arguments.First();
    var compilers = dafnyOptions.Plugins.SelectMany(p => p.GetCompilers()).ToList();
    var compiler = compilers.LastOrDefault(c => c.TargetId == target);
    if (compiler == null) {
      var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetLanguage})"));
      return new FailedOption($"No compiler found for compileTarget \"{target}\"; expecting one of {known}");
    }

    return new ParsedOption(1, compiler);
  }

  public override void PostProcess(DafnyOptions options) {
    options.Compiler = Get(options);
    base.PostProcess(options);
  }
}