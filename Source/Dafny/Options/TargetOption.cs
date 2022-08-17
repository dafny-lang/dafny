using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

public class TargetOption : StringOption {
  public static readonly TargetOption Instance = new();

  public override object DefaultValue => "cs";

  public override string LongName => "target";
  public override string ShortName => "t";
  public override string ArgumentName => "language";
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

  protected override string[] AllowedValues => new[] { "cs", "go", "js", "java", "py", "cpp" };

  public override ParseOptionResult Parse(DafnyOptions dafnyOptions, Stack<string> arguments) {
    var target = arguments.Pop();
    var compilers = dafnyOptions.Plugins.SelectMany(p => p.GetCompilers()).ToList();
    var compiler = compilers.LastOrDefault(c => c.TargetId == target);
    if (compiler == null) {
      var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetLanguage})"));
      return new FailedOption($"No compiler found for compileTarget \"{target}\"; expecting one of {known}");
    }

    return new ParsedOption(compiler);
  }

  public override string TypedPostProcess(DafnyOptions options, string value) {
    var compilers = options.Plugins.SelectMany(p => p.GetCompilers()).ToList();
    var compiler = compilers.LastOrDefault(c => c.TargetId == value);
    if (compiler == null) {
      var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetLanguage})"));
      return $"No compiler found for compileTarget \"{value}\"; expecting one of {known}";
    }
    options.Compiler = compiler;
    return base.TypedPostProcess(options, value);
  }
}
