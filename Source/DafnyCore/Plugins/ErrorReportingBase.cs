using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Plugins; 

/// <summary>
/// Abstract base class for plugin interfaces that may report errors.
/// </summary>
public abstract class ErrorReportingBase {
  /// <summary>
  /// Used to report errors and warnings, with positional information.
  /// </summary>
  protected readonly ErrorReporter Reporter;

  /// <summary>
  /// Constructor that accepts an ErrorReporter
  /// You can obtain an ErrorReporter in either of the two following ways:
  /// * Extend a PluginConfiguration class, and override the appropriate Get***() method whose first argument is an ErrorReporter
  /// * Have no PluginConfiguration class, and an ErrorReporter will be provided to your class's constructor.
  /// 
  /// Then you can use the protected field "reporter" like the following:
  /// 
  ///     reporter.Error(MessageSource.Compiler, token, "[Your plugin] Your error message here");
  ///
  /// The token is usually obtained on expressions and statements in the field `tok`
  /// If you do not have access to them, use program.GetFirstTopLevelToken()
  /// </summary>
  /// <param name="reporter">The error reporter. Usually outputs automatically to IDE or command-line</param>
  public ErrorReportingBase(ErrorReporter reporter) {
    Contract.Requires(reporter != null);
    Reporter = reporter;
  }
}