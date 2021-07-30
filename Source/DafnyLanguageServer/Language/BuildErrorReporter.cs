using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// The class <see cref="ErrorReporter"/> is abstract; thus, it cannot be used directly.
  /// However, since there are no abstract members, we simply inherit from it since it provides
  /// all the necessary functionallity already.
  /// </summary>
  public class BuildErrorReporter : ErrorReporter {
    /// <summary>
    /// Gets if the error reporter receive any error messages.
    /// </summary>
    public bool HasErrors => AllMessages[ErrorLevel.Error].Count > 0;

    // TODO this method is only overriden because the base class does not set propery "source" of "ErrorMessage".
    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      if(ErrorsOnly && level != ErrorLevel.Error) {
        // discard the message
        return false;
      }
      AllMessages[level].Add(new ErrorMessage { source = source, token = tok, message = msg });
      return true;
    }
  }
}
