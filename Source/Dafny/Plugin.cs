using System;
using System.Linq;
using System.Reflection;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

/// <summary>
/// This class is internal to Dafny. It wraps an assembly and an extracted configuration from this assembly,
/// The configuration provides the methods to parse command-line arguments and obtain Rewriters 
/// </summary>
public class Plugin {
  private readonly Assembly assembly;
  public readonly Configuration Configuration;

  class AutomaticConfiguration : Configuration {
    private Func<ErrorReporter, Rewriter>[] rewriters;
    public AutomaticConfiguration(Func<ErrorReporter, Rewriter>[] rewriters) {
      this.rewriters = rewriters;
    }

    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
      return rewriters.Select(funcErrorReporterRewriter =>
        funcErrorReporterRewriter(errorReporter)).ToArray();
    }
  }

  public Plugin(string pluginPath, string[] args, ErrorReporter reporter) {
    assembly = Assembly.LoadFrom(pluginPath);

    System.Type[] rewriterTypes = assembly.GetTypes().Where(t =>
      t.IsAssignableTo(typeof(Rewriter))).ToArray();
    // Checks about the plugin to be well-behaved.
    if (!rewriterTypes.Any()) {
      throw new Exception($"Plugin {pluginPath} does not contain any Microsoft.Dafny.Plugins.Rewriter");
    }

    foreach (var configurationType in assembly.GetTypes()
               .Where(t => t.IsAssignableTo(typeof(Configuration)))) {
      if (Configuration != null) {
        throw new Exception($"Only one class should extend Microsoft.Dafny.Plugins.Configuration from {pluginPath}. Please remove {configurationType}.");
      }
      Configuration = Activator.CreateInstance(configurationType) as Configuration;

      if (Configuration == null) {
        throw new Exception($"Could not instantiate a {configurationType} from {pluginPath}");
      }
      Configuration.ParseArguments(args);
    }

    Configuration ??= new AutomaticConfiguration(
      rewriterTypes.Select<System.Type, Func<ErrorReporter, Rewriter>>((System.Type rewriterType) =>
        (ErrorReporter errorReporter) =>
          Activator.CreateInstance(rewriterType, new object[] { errorReporter }) as Rewriter).ToArray());
  }
}