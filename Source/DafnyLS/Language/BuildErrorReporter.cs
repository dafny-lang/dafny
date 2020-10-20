using Microsoft.Dafny;

namespace DafnyLS.Language {
  /// <summary>
  /// The class <see cref="ErrorReporter"/> is abstract; thus, it cannot be used directly.
  /// However, since there are no abstract members, we simply inherit from it since it provides
  /// all the necessary functionallity already.
  /// </summary>
  public class BuildErrorReporter : ErrorReporter {
  }
}
