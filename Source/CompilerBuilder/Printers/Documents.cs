namespace CompilerBuilder;

public interface Document {
  public void Render(TextWriter writer, int desiredWidth = 120) {
    Render(0, desiredWidth, writer);
  }
  
  // TODO make internal
  public void Render(int indentation, int desiredWidth, TextWriter writer);
}

record Verbatim(string Value) : Document {
  public void Render(int indentation, int desiredWidth, TextWriter writer) {
    writer.Write(Value);
  }
}

record Indent(Document Inner, int Amount) : Document {
  public void Render(int indentation, int desiredWidth, TextWriter writer) {
    Inner.Render(indentation + Amount, desiredWidth, writer);
  }
}

record Empty : Document {
  public void Render(int indentation, int desiredWidth, TextWriter writer) {
  }
}

public enum Orientation {
  Horizontal,
  Vertical,
  HorizontalIfPossible,
};

record SequenceD(Document Left, Document Right, Orientation Orientation) : Document {
  public void Render(int indentation, int desiredWidth, TextWriter writer) {
    if (Orientation == Orientation.Horizontal) {
      Left.Render(indentation, desiredWidth, writer);
      Right.Render(indentation, desiredWidth, writer);
    } else if (Orientation == Orientation.Vertical) {
      Left.Render(indentation, desiredWidth, writer);
      writer.Write(new string(' ', indentation));
      writer.WriteLine();
      Right.Render(indentation, desiredWidth, writer);
    } else {
      throw new NotImplementedException();
      // Left.Render(indentation, desiredWidth, writer);
      // if (writer.Column + Right.Width > desiredWidth) {
      //   writer.Write(new string(' ', indentation));
      //   writer.WriteLine();
      // }
      // Right.Render(indentation, desiredWidth, writer);
    }
  }
}