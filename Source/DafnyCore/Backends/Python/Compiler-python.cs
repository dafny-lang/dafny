using System.Collections.ObjectModel;
using System.Diagnostics;
using System.IO;
using System.Text.RegularExpressions;

namespace ExtensionMethods {
  using Microsoft.Dafny;
  public static class PythonExtensions {
    public static ConcreteSyntaxTree NewBlockPy(this ConcreteSyntaxTree tree, string header = "", string footer = "",
      BlockStyle open = BlockStyle.Newline,
      BlockStyle close = BlockStyle.Nothing) {
      return tree.NewBlock(header, footer, open, close);
    }
  }
}

namespace Microsoft.Dafny.Compilers {
}
