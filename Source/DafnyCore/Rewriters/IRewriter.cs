// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Diagnostics.Contracts;
using static Microsoft.Dafny.RewriterErrors;

namespace Microsoft.Dafny {
  /// <summary>
  /// Internal rewriters used in the resolution pipeline
  /// </summary>
  public abstract class IRewriter {
    /// <summary>
    /// Used to report errors and warnings, with positional information.
    /// </summary>
    protected ErrorReporter Reporter;

    protected DafnyOptions Options => Reporter.Options;

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
    /// If you do not have access to them, use moduleDefinition.GetStartOfFirstFileToken()
    /// </summary>
    /// <param name="reporter">The error reporter. Usually outputs automatically to IDE or command-line</param>
    protected internal IRewriter(ErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.Reporter = reporter;
    }

    /// <summary>
    /// Phase 1/8
    /// Override this method to obtain the initial program after parsing and built-in pre-resolvers.
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="program">The entire program</param>
    internal virtual void PreResolve(Program program) {
      Contract.Requires(program != null);
    }

    /// <summary>
    /// Phase 2/8
    /// Override this method to obtain a module definition after parsing and built-in pre-resolvers.
    /// You can then report errors using reporter.Error(MessageSource.Resolver, token, "message") (see above)
    /// This is a good place to perform AST rewritings, if necessary
    /// </summary>
    /// <param name="moduleDefinition">A module definition before is resolved</param>
    internal virtual void PreResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 3/8
    /// Override this method to obtain a module definition after bare resolution, if no error were thrown.
    /// You can then report errors using reporter.Error (see above)
    /// We heavily discourage AST rewriting after this stage, as automatic type checking will not take place anymore.
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it is resolved and type-checked</param>
    internal virtual void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 5/8
    /// Override this method to obtain the module definition after resolution and
    /// SCC/Cyclicity/Recursivity analysis.
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    ///   is resolved, type-checked and SCC/Cyclicity/Recursivity have been performed</param>
    /// <param name="errorReporter"></param>
    internal virtual void PostCyclicityResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 6/8
    /// Override this method to obtain the module definition after the phase decreasesResolve
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    /// is resolved, type-checked and SCC/Cyclicity/Recursivity and decreasesResolve checks have been performed</param>
    internal virtual void PostDecreasesResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 7/8
    /// Override this method to obtain a module definition after the entire resolution pipeline
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="moduleDefinition">A module definition after it
    /// is resolved, type-checked and SCC/Cyclicity/Recursivity have been performed</param>
    internal virtual void PostResolve(ModuleDefinition moduleDefinition) {
      Contract.Requires(moduleDefinition != null);
    }

    /// <summary>
    /// Phase 8/8
    /// Override this method to obtain the final program after the entire resolution pipeline
    /// after the individual PostResolve on every module
    /// You can then report errors using reporter.Error (see above)
    /// </summary>
    /// <param name="program">The entire program after it is fully resolved</param>
    internal virtual void PostResolve(Program program) {
      Contract.Requires(program != null);
    }

    internal virtual void PreVerify(ModuleDefinition module) {
      Contract.Requires(module != null);
    }

    public virtual void PostVerification(Program program) {
      Contract.Requires(program != null);
    }

    public virtual void ReportWarning(ErrorId errorId, IOrigin t, params object[] messageParts) {
      Reporter.Warning(MessageSource.Rewriter, errorId, t, messageParts);
    }

    public virtual void ReportError(ErrorId errorId, IOrigin t, params object[] messageParts) {
      Reporter.Error(MessageSource.Rewriter, errorId, t, messageParts);
    }
  }
}
