using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Plugins {
  /// <summary>
  /// A class that plugins should extend, in order to provide an extra Rewriter to the pipeline.
  ///
  /// If the plugin defines no Configuration, then Dafny will instantiate every sub-class
  /// of Rewriter from the plugin, providing them with an ErrorReporter as the first and only argument.
  /// </summary>
  public abstract class Rewriter {
    /// <summary>
    /// Used to report errors and warnings, with positional information.
    /// </summary>
    protected readonly ErrorReporter Reporter;

    /// <summary>
    /// Constructor that accepts an ErrorReporter
    /// You can obtain an ErrorReporter two following ways:
    /// * Extend a Configuration class, and override the method GetRewriters(), whose first argument is an ErrorReporter
    /// * Have no Configuration  class, and an ErrorReporter will be provided to your class's constructor.
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
      this.Reporter = reporter;
    }

    /// <summary>
    /// Phase 1/5
    /// Override this method to obtain a module definition after parsing and built-in pre-resolvers,
    /// You can then report errors using reporter.Error(MessageSource.Resolver, token, "message") (see above)
    /// This is a good place to perform AST rewritings, if necessary
    /// </summary>
    /// <param name="moduleDefinition">A module definition before is resolved</param>
    public virtual void PreResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 2/5
    /// Override this method to obtain a module definition after bare resolution, if no error were thrown,
    /// You can then report errors using reporter.Error (see above)
    /// We heavily discourage AST rewriting after this stage, as automatic type checking will not take place anymore.
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it is resolved and type-checked</param>
    public virtual void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 3/5
    /// Override this method to obtain the module definition after resolution and
    /// SCC/Cyclicity/Recursivity analysis.
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    /// is resolved, type-checked and SCC/Cyclicity/Recursivity have been performed</param>
    public virtual void PostCyclicityResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 4/5
    /// Override this method to obtain the module definition after resolving decreasesResolve
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    /// is resolved, type-checked and SCC/Cyclicity/Recursivity and decreasesResolve checks have been performed</param>
    public virtual void PostDecreasesResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 5/5
    /// Override this method to obtain a module definition after the entire resolution pipeline
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    /// is resolved, type-checked and SCC/Cyclicity/Recursivity have been performed</param>
    public virtual void PostResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 5/5
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