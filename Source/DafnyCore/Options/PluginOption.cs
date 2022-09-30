using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class PluginOption : CommandLineOption<List<string>>, ILegacyOption {
  public static readonly PluginOption Instance = new();
  public override object DefaultValue => new List<string>();
  public override string LongName => "plugin";
  public override string ArgumentName => "path-to-one-assembly[,argument]*";
  public string Category => "Plugins";
  public string LegacyName => LongName;

  public override string Description => @"
(experimental) One path to an assembly that contains at least one
instantiatable class extending Microsoft.Dafny.Plugin.Rewriter. It
can also extend Microsoft.Dafny.Plugins.PluginConfiguration to
receive arguments. More information about what plugins do and how
to define them:

https://github.com/dafny-lang/dafny/blob/master/Source/DafnyLanguageServer/README.md#about-plugins";

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
    var plugins = Get(options);
    foreach (var pluginAndArgument in plugins) {
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

    return null;
  }
}
