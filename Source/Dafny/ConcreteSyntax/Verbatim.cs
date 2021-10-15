using System.Collections.Generic;
using System.IO;
using System.Text;

namespace Microsoft.Dafny {
  public class Verbatim : StringWriter, ICanRender {
    public void Render(TextWriter writer, int indentation, WriterState writerState, Queue<FileSyntax> files) {
      writer.Write(ToString());
    }
  }
}