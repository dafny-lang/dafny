using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

/// <summary>
/// This class is internal to Dafny. It wraps an assembly and an extracted configuration from this assembly,
/// The configuration provides the methods to parse command-line arguments and obtain Rewriters 
/// </summary>
public class Plugin {
  public Configuration Configuration;

  private readonly string path;
  private readonly Assembly assembly;
  private System.Type[] rewriterTypes;

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

  public static IEnumerable<System.Type> GetConfigurationsTypes(Assembly assembly) {
    return assembly.GetTypes()
      .Where(t => t.IsAssignableTo(typeof(Configuration)));
  }

  public Plugin(string pluginPath, string[] args, ErrorReporter reporter) {
    path = pluginPath;
    assembly = Assembly.LoadFrom(path);
    rewriterTypes = CheckPluginForRewriters(assembly, path);
    Configuration = LoadConfiguration(assembly, args, path, rewriterTypes);
  }

  private static System.Type[] CheckPluginForRewriters(Assembly assembly, string path) {
    System.Type[] rewriterTpes = assembly.GetTypes().Where(t =>
      t.IsAssignableTo(typeof(Rewriter))).ToArray();
    // Checks about the plugin to be well-behaved.
    if (!rewriterTpes.Any()) {
      throw new Exception($"Plugin {path} does not contain any Microsoft.Dafny.Plugins.Rewriter");
    }

    return rewriterTpes;
  }

  private static Configuration LoadConfiguration(Assembly assembly, string[] args, string path, System.Type[] rewriterTypes) {
    Configuration configuration = null;
    foreach (var configurationType in GetConfigurationsTypes(assembly)) {
      if (configuration != null) {
        throw new Exception(
          $"Only one class should extend Microsoft.Dafny.Plugins.Configuration from {path}. Please remove {configurationType}.");
      }

      configuration = (Configuration)Activator.CreateInstance(configurationType);

      if (configuration == null) {
        throw new Exception($"Could not instantiate a {configurationType} from {path}");
      }

      configuration.ParseArguments(args);
    }

    configuration ??= new AutomaticConfiguration(
      rewriterTypes.Select<System.Type, Func<ErrorReporter, Rewriter>>((System.Type rewriterType) =>
        (ErrorReporter errorReporter) =>
          Activator.CreateInstance(rewriterType, new object[] { errorReporter }) as Rewriter).ToArray());
    return configuration;
  }
}