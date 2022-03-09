﻿//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.Plugins;

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
public abstract class PluginConfiguration {
  /// <summary>
  /// A Microsoft.Dafny.Plugins.PluginConfiguration will be automatically instantiated an arguments
  /// will be provided to the plugin by the method `ParseArguments``;
  /// </summary>
  /// <param name="args">The arguments passed to the plugin</param>
  public virtual void ParseArguments(string[] args) {
  }

  /// <summary>
  /// Override this method to provide rewriters
  /// </summary>
  /// <returns>a list of Rewriter that are going to be used in the resolution pipeline</returns>
  public virtual Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return Array.Empty<Rewriter>();
  }

  /// <summary>
  /// Override this method to provide specific compilers to Dafny
  /// </summary>
  /// <returns>A list of compilers implemented by this plugin</returns>
  public virtual Compiler[] GetCompilers() {
    return Array.Empty<Compiler>();
  }
}