using Microsoft.Dafny;

namespace DafnyCore.Backends.Python;

public static class PythonExtensions {
  public static ConcreteSyntaxTree NewBlockPy(this ConcreteSyntaxTree tree, string header = "", string footer = "",
    BlockStyle open = BlockStyle.Newline,
    BlockStyle close = BlockStyle.Nothing) {
    return tree.NewBlock(header, footer, open, close);
  }
}