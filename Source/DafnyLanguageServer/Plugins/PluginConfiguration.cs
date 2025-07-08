// SPDX-License-Identifier: MIT
using System;
using OmniSharp.Extensions.LanguageServer.Server;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Plugins should define a class that extends PluginConfiguration,
/// in order to receive plugin-specific command-line arguments by overwriting the method `ParseArguments`
/// It is also used to provide to Dafny a list of Rewriter instances using the method `GetRewriters`, and Compiler
/// instances using `GetCompilers`
///
/// If the plugin defines no PluginConfiguration, then Dafny will instantiate every sub-class
/// of Rewriter and Compiler from the plugin (providing rewriters with an ErrorReporter in the constructor
/// as the first and only argument, and compilers with no arguments).
/// </summary>
public abstract class PluginConfiguration : Dafny.Plugins.PluginConfiguration {
  /// <summary>
  /// Override this method to provide quick fixers
  /// </summary>
  /// <returns>An array of quick fixers implemented by this plugin</returns>
  public virtual DafnyCodeActionProvider[] GetDafnyCodeActionProviders() {
    return [];
  }

  /// <summary>
  /// Override this method to provide additional language server handlers
  /// </summary>
  /// <returns>The provided LanguageServerOptions with the additional handlers applied</returns>
  public virtual LanguageServerOptions WithPluginHandlers(LanguageServerOptions options) {
    return options;
  }
}
