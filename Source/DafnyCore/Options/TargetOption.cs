using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

public class TargetOption : StringOption, ILegacyOption {
  public static readonly TargetOption Instance = new();
  public override object DefaultValue => "cs";
  public override string LongName => "target";
  public string LegacyName => "compileTarget";
  public override string ShortName => "t";
  public override string ArgumentName => "language";
  public string Category => "Compilation options";

  public override string Description => @"
cs (default) - Compile to .NET via C#.
go - Compile to Go.
js - Compile to JavaScript.
java - Compile to Java.
py - Compile to Python.
cpp - Compile to C++.

Note that the C++ backend has various limitations (see
Docs/Compilation/Cpp.md). This includes lack of support for
BigIntegers (aka int), most higher order functions, and advanced
features like traits or co-inductive types.".TrimStart();

  protected override string[] AllowedValues => new[] { "cs", "go", "js", "java", "py", "cpp" };

  public override string PostProcess(DafnyOptions options) {
    var value = Get(options);
    var compilers = options.Plugins.SelectMany(p => p.GetCompilers()).ToList();
    var compiler = compilers.LastOrDefault(c => c.TargetId == value);
    if (compiler == null) {
      var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetLanguage})"));
      return $"No compiler found for compileTarget \"{value}\"; expecting one of {known}";
    }
    options.Compiler = compiler;
    return null;
  }
}
