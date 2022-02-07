using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.Plugins;

/// <summary>
/// Plugins should define a class that extends PluginConfiguration,
/// in order to receive plugin-specific command-line arguments by overwriting the method `ParseArguments`
/// It is also used to provide to Dafny a list of Rewriter using the method `GetRewriters`
///
/// If the plugin defines no PluginConfiguration, then Dafny will instantiate every sub-class
/// of Rewriter from the plugin, providing them with an ErrorReporter in the constructor
/// as the first and only argument.
/// </summary>
public abstract class PluginConfiguration {
  /// <summary>
  /// A Microsoft.Dafny.Plugins.PluginConfiguration will be automatically instantiated an arguments
  /// will be provided to the plugin by the method `ParseArguments``;
  /// </summary>
  /// <param name="args">The arguments passed to the plugin</param>
  public virtual void ParseArguments(string[] args) {
  }

  /// <summary>
  /// Override this method to provide specific rewriters to Dafny
  /// </summary>
  /// <returns>a list of Rewriter that are going to be used in the resolution pipeline</returns>
  public virtual Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return Array.Empty<Rewriter>();
  }
}
