using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Dafny;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class PluginOption : CommandLineOption<List<string>> {
  public override object DefaultValue { get; }
  public override string LongName { get; }
  public override string ArgumentName { get; }
  public override string Category { get; }
  public override string Description { get; }
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    if (ps.ConfirmArgumentCount(1)) {
      var pluginAndArgument = ps.args[ps.i];
      if (pluginAndArgument.Length > 0) {
        var pluginArray = pluginAndArgument.Split(',');
        var pluginPath = pluginArray[0];
        var arguments = Array.Empty<string>();
        if (pluginArray.Length >= 2) {
          // There are no commas in paths, but there can be in arguments
          var argumentsString = string.Join(',', pluginArray.Skip(1));
          // Parse arguments, accepting and remove double quotes that isolate long arguments
          arguments = ParsePluginArguments(argumentsString);
        }

        options.Plugins.Add(AssemblyPlugin.Load(pluginPath, arguments));
      }
    }
  }

  private static string[] ParsePluginArguments(string argumentsString) {
    var splitter = new Regex(@"""(?<escapedArgument>(?:[^""\\]|\\\\|\\"")*)""|(?<rawArgument>[^ ]+)");
    var escapedChars = new Regex(@"(?<escapedDoubleQuote>\\"")|\\\\");
    return splitter.Matches(argumentsString).Select(
      matchResult =>
        matchResult.Groups["escapedArgument"].Success
          ? escapedChars.Replace(matchResult.Groups["escapedArgument"].Value,
            matchResult2 => matchResult2.Groups["escapedDoubleQuote"].Success ? "\"" : "\\")
          : matchResult.Groups["rawArgument"].Value
    ).ToArray();
  }

  public override string PostProcess(DafnyOptions options) {
    throw new System.NotImplementedException();
  }
}

public class CompileVerboseOption : BooleanOption {
  public static readonly CompileVerboseOption Instance = new();
  public override string LongName => "compileVerbose";
  public override string Category => "Compilation options";
  public override string Description => @"
0 - don't print status of compilation to the console
1 (default) - print information such as files being written by
    the compiler to the console";
  public override string PostProcess(DafnyOptions options) {
    options.CompileVerbose = Get(options);
    return null;
  }
}

class PrintModeOption : CommandLineOption<DafnyOptions.PrintModes> {
  public static readonly PrintModeOption Instance = new();
  public override bool Hidden => true;

  public override object DefaultValue => DafnyOptions.PrintModes.Everything;
  public override string LongName => "printMode";
  public override string ShortName => null;
  public override string ArgumentName => "Everything|DllEmbed|NoIncludes|NoGhost";
  public override string Category => "Overall reporting and printing";

  public override string Description => @"
Everything is the default.
DllEmbed prints the source that will be included in a compiled dll.
NoIncludes disables printing of {{:verify false}} methods incorporated via the
include mechanism, as well as datatypes and fields included from other files.
NoGhost disables printing of functions, ghost methods, and proof statements in
implementation methods.  It also disables anything NoIncludes disables.";
  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    if (ps.ConfirmArgumentCount(1)) {
      if (ps.args[ps.i].Equals("Everything")) {
        Set(options, DafnyOptions.PrintModes.Everything);
      } else if (ps.args[ps.i].Equals("NoIncludes")) {
        Set(options, DafnyOptions.PrintModes.NoIncludes);
      } else if (ps.args[ps.i].Equals("NoGhost")) {
        Set(options, DafnyOptions.PrintModes.NoGhost);
      } else if (ps.args[ps.i].Equals("DllEmbed")) {
        Set(options, DafnyOptions.PrintModes.DllEmbed);
      } else {
        InvalidArgumentError(LongName, ps);
      }
    }
  }
  public override string PostProcess(DafnyOptions options) {
    options.PrintMode = Get(options);
    return null;
  }
}
class DafnyPreludeOption : StringOption {
  public static readonly DafnyPreludeOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "dprelude";
  public override string ShortName => null;
  public override string ArgumentName => "file";
  public override string Category => "Input configuration";
  public override string Description => "choose Dafny prelude file";

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrelude = Get(options);
    return null;
  }
}

public class LibraryOption : CommandLineOption<List<string>> {
  public static readonly LibraryOption Instance = new();

  public override object DefaultValue => new List<string>();
  public override string LongName => "library";
  public override string ShortName => null;
  public override string ArgumentName => null;
  public override string Category => "Compilation options";
  public override string Description => @"
The contents of this file and any files it includes can be referenced from other files as if they were included. 
However, these contents are skipped during code generation and verification.
This option is useful in a diamond dependency situation, 
to prevent code from the bottom dependency from being generated more than once.".TrimStart();

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    var value = Get(options) ?? new List<string>();
    if (ps.ConfirmArgumentCount(1)) {
      value.Add(ps.args[ps.i]);
    }

    Set(options, value);
  }

  public override string PostProcess(DafnyOptions options) {
    options.LibraryFiles = Get(options).ToHashSet();
    return null;
  }
}
