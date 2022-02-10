using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

/// <summary>
/// This class wraps an assembly and an extracted configuration from this assembly,
/// The configuration provides the methods to parse command-line arguments and obtain Rewriters 
/// </summary>
public record Plugin(Assembly Assembly, string[] Args) {
  public PluginConfiguration PluginConfiguration { get; } = LoadConfiguration(Assembly, Args);

  public static Plugin Load(string pluginPath, string[] args) {
    return new Plugin(Assembly.LoadFrom(pluginPath), args);
  }

  class AutomaticPluginConfiguration : PluginConfiguration {
    public Func<ErrorReporter, Rewriter>[] Rewriters { get; init; }
    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
      return Rewriters.Select(funcErrorReporterRewriter =>
        funcErrorReporterRewriter(errorReporter)).ToArray();
    }
  }

  public static IEnumerable<System.Type> GetConfigurationsTypes(Assembly assembly) {
    return assembly.GetTypes()
      .Where(type => type.IsAssignableTo(typeof(PluginConfiguration)));
  }

  private static System.Type[] CheckPluginForRewriters(Assembly assembly) {
    var rewriterTypes = assembly.GetTypes().Where(type =>
      type.IsAssignableTo(typeof(Rewriter))).ToArray();
    // Checks about the plugin to be well-behaved.
    if (!rewriterTypes.Any()) {
      throw new Exception($"Plugin {assembly.Location} does not contain any Microsoft.Dafny.Plugins.Rewriter");
    }

    return rewriterTypes;
  }

  private static PluginConfiguration LoadConfiguration(Assembly assembly, string[] args) {
    var rewriterTypes = CheckPluginForRewriters(assembly);
    PluginConfiguration pluginConfiguration = null;
    foreach (var configurationType in GetConfigurationsTypes(assembly)) {
      if (pluginConfiguration != null) {
        throw new Exception(
          $"Only one class should extend Microsoft.Dafny.Plugins.PluginConfiguration from {assembly.Location}. Please remove {configurationType}.");
      }

      pluginConfiguration = (PluginConfiguration)Activator.CreateInstance(configurationType);

      if (pluginConfiguration == null) {
        throw new Exception($"Could not instantiate a {configurationType} from {assembly.Location}");
      }

      pluginConfiguration.ParseArguments(args);
    }

    pluginConfiguration ??= new AutomaticPluginConfiguration {
      Rewriters = rewriterTypes.Select(CreateRewriterFactory).ToArray()
    };
    return pluginConfiguration;
  }

  private static Func<ErrorReporter, Rewriter> CreateRewriterFactory(System.Type rewriterType) {
    return errorReporter => (Rewriter)Activator.CreateInstance(rewriterType, new object[] { errorReporter });
  }

  public IEnumerable<IRewriter> GetRewriters(ErrorReporter reporter) {
    return PluginConfiguration.GetRewriters(reporter).Select(rewriter => new PluginRewriter(reporter, rewriter));
  }
}