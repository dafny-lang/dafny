using System.Collections.Generic;
using System.IO;

namespace Microsoft.Dafny {
  public class WriterState {
    public bool HasNewLine { get; set; }
  }

  public interface ICanRender {
    void Render(TextWriter writer, int indentation, WriterState writerState, Queue<FileSyntax> files, int indentSize = 2);
  }
}