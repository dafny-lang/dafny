using System.Collections.Generic;
using System.IO;

namespace Microsoft.Dafny {
  class NewLine : ICanRender {
    public void Render(TextWriter writer, int indentation, WriterState writerState, Queue<FileSyntax> files, int indentSize = 2) {
      writerState.HasNewLine = true;
      writer.WriteLine();
    }
  }
}