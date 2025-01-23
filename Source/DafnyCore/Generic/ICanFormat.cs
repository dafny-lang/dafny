namespace Microsoft.Dafny;

public interface ICanFormat : INode {
  /// Sets the indentation of individual tokens owned by this node, given
  /// the new indentation set by the tokens preceding this node
  /// Returns if further traverse needs to occur (true) or if it already happened (false)
  bool SetIndent(int indentBefore, TokenNewIndentCollector formatter);
}