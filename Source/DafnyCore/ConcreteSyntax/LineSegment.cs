using System.Collections.Generic;
using System.IO;

namespace Microsoft.Dafny {

  class LineSegment : ICanRender {
    private readonly string _value;

    public LineSegment(string value) {
      this._value = value;
    }

    public static implicit operator LineSegment(string value) => new LineSegment(value);

    public void Render(TextWriter writer, int indentation, WriterState writerState, Queue<FileSyntax> files, int indentSize = 2) {
      if (writerState.HasNewLine) {
        writer.Write(new string(' ', indentation));
        writerState.HasNewLine = false;
      }

      writer.Write(_value);
    }
  }
}