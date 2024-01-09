namespace Microsoft.Dafny.Plugins;

public abstract class DocstringRewriter {
  /// Retrieves the content of what Dafny believes is the Docstring
  /// and filters it. Note that the default rendering in VSCode is Markdown,
  /// so since it's the major IDE that Dafny supports, you probably want to
  /// have your docstring converter converts parts of the code to Markdown
  /// As an example:
  /// ```
  /// function Test(i: int): int
  /// // Returns the number of
  /// // numbers smaller than i
  /// { ... }
  /// ```
  /// The argument docstring will contain "Returns the number of\nnumbers smaller than i"
  public virtual string RewriteDocstring(string extractedDocString) {
    return extractedDocString;
  }
}