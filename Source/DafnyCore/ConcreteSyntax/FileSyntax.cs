using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Dafny {
  public class FileSyntax : ICanRender {
    public readonly string Filename;

    public FileSyntax(string filename) {
      Contract.Requires(filename != null);
      Filename = filename;
      Tree = new ConcreteSyntaxTree();
    }

    public ConcreteSyntaxTree Tree { get; }

    public void Render(TextWriter writer, int indentation, WriterState writerState, Queue<FileSyntax> files, int indentSize = 2) {
      files.Enqueue(this);
    }
  }
}