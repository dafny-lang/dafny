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
  public abstract class Rewriter {
    /// <summary>
    /// Used to report errors and warnings, with positional information.
    /// </summary>
    protected readonly ErrorReporter Reporter;

    /// <summary>
    /// Constructor that accepts an ErrorReporter
    /// You can obtain an ErrorReporter two following ways:
    /// * Extend a PluginConfiguration class, and override the method GetRewriters(), whose first argument is an ErrorReporter
    /// * Have no PluginConfiguration  class, and an ErrorReporter will be provided to your class's constructor.
    /// 
    /// Then you can use the protected field "reporter" like the following:
    /// 
    ///     reporter.Error(MessageSource.Compiler, token, "[Your plugin] Your error message here");
    ///
    /// The token is usually obtained on expressions and statements in the field `tok`
    /// If you do not have access to them, use moduleDefinition.GetFirstTopLevelToken()
    /// </summary>
    /// <param name="reporter">The error reporter. Usually outputs automatically to IDE or command-line</param>
    public Rewriter(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      Reporter = reporter;
    }
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
