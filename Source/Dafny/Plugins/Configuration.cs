using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.Plugins;

/// <summary>
/// A class that plugins should extend, in order to receive plugin-specific command-line arguments
///
/// If no class extending Microsoft.Dafny.Plugins.Configuration is defined in the assembly plugin,
/// Dafny will implicitly load all classes extending Rewriter
/// providing them with an ErrorReporter as the first and only argument
/// </summary>
public abstract class Configuration {
  /// <summary>
  /// A Microsoft.Dafny.Plugins.Configuration will be automatically instantiated an arguments
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