// SPDX-License-Identifier: MIT
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Plugins {
  /// <summary>
  /// A class that plugins should extend, in order to provide an extra Rewriter to the pipeline.
  ///
  /// If the plugin defines no PluginConfiguration, then Dafny will instantiate every sub-class
  /// of Rewriter from the plugin, providing them with an ErrorReporter in the constructor
  /// as the first and only argument.
  /// </summary>
  public abstract class Rewriter : ErrorReportingBase {
    public Rewriter(ErrorReporter reporter) : base(reporter) { }

    /// <summary>
    /// Override this method to obtain a module definition after the entire resolution pipeline
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    /// is resolved, type-checked and SCC/Cyclicity/Recursivity have been performed</param>
    public virtual void PostResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Override this method to obtain the final program after the entire resolution pipeline
    /// after the individual PostResolve on every module
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="program">The entire program after it is fully resolved</param>
    public virtual void PostResolve(Program program) {
      Contract.Requires(program != null);
    }
  }
}
