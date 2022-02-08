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
  public PluginConfiguration PluginConfiguration { get; init; } = LoadConfiguration(Assembly, Args);

  public static Plugin Load(string pluginPath, string[] args) {
    return new Plugin(Assembly.LoadFrom(pluginPath), args);
  }

  class AutomaticPluginConfiguration : PluginConfiguration {
    private Func<ErrorReporter, Rewriter>[] rewriters;
    public AutomaticPluginConfiguration(Func<ErrorReporter, Rewriter>[] rewriters) {
      this.rewriters = rewriters;
    }

    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
      return rewriters.Select(funcErrorReporterRewriter =>
        funcErrorReporterRewriter(errorReporter)).ToArray();
    }
  }

  public static IEnumerable<System.Type> GetConfigurationsTypes(Assembly assembly) {
    return assembly.GetTypes()
      .Where(t => t.IsAssignableTo(typeof(PluginConfiguration)));
  }

  private static System.Type[] CheckPluginForRewriters(Assembly assembly) {
    System.Type[] rewriterTpes = assembly.GetTypes().Where(t =>
      t.IsAssignableTo(typeof(Rewriter))).ToArray();
    // Checks about the plugin to be well-behaved.
    if (!rewriterTpes.Any()) {
      throw new Exception($"Plugin {assembly.Location} does not contain any Microsoft.Dafny.Plugins.Rewriter");
    }

    return rewriterTpes;
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

    pluginConfiguration ??= new AutomaticPluginConfiguration(
      rewriterTypes.Select<System.Type, Func<ErrorReporter, Rewriter>>((System.Type rewriterType) =>
        (ErrorReporter errorReporter) =>
          Activator.CreateInstance(rewriterType, new object[] { errorReporter }) as Rewriter).ToArray());
    return pluginConfiguration;
  }

  public IEnumerable<IRewriter> GetRewriters(ErrorReporter reporter) {
    return PluginConfiguration.GetRewriters(reporter).Select(rewriter => new PluginRewriter(reporter, rewriter));
  }
}