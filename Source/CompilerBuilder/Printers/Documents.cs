namespace CompilerBuilder;

public interface Document {
  public void Render(TextWriter writer, int desiredWidth = 120) {
    Render(desiredWidth, new IndentationWriter(writer, 2));
  }
  
  // TODO make internal
  public void Render(int desiredWidth, IndentationWriter writer);
  public bool IsEmpty { get; }

  public Document Indent(int amount) {
    return this is Empty ? this : new IndentD(this, amount);
  }
  
  public Document Then(Document next, Orientation orientation) {
    if (this is Empty) {
      return next;
    }

    if (next is Empty) {
      return this;
    }

    return new SequenceD(this, next, orientation);
  }
}

record Verbatim(string Value) : Document {
  public void Render(int desiredWidth, IndentationWriter writer) {
    writer.Write(Value);
  }

  public bool IsEmpty => !Value.Any();
}

record IndentD(Document Inner, int Amount) : Document {
  public void Render(int desiredWidth, IndentationWriter writer) {
    writer.Indent();
    Inner.Render(desiredWidth, writer);
    writer.Undent();
  }

  public bool IsEmpty => Inner.IsEmpty;
}

record Empty : Document {
  public void Render(int desiredWidth, IndentationWriter writer) {
  }

  public bool IsEmpty => true;
}

public enum Orientation {
  Adjacent,
  Spaced,
  Vertical,
  LineBroken,
  SpacedOrVertical,
}

public class IndentationWriter(TextWriter writer, int spacesPerTick) {
  private bool startOfLine = true;
  private int indentationTicks = 0;
  public int LineWidth { get; private set; } = 0;

  public void Write(string value) {
    if (startOfLine) {
      var spaces = new string(' ', indentationTicks * spacesPerTick);
      LineWidth += spaces.Length;
      writer.Write(spaces);
    }
    writer.Write(value);
    LineWidth += value.Length;
    startOfLine = false;
  }

  public void WriteLine() {
    writer.WriteLine();
    startOfLine = true;
    LineWidth = 0;
  }

  public void Indent() {
    indentationTicks++;
  }
  
  public void Undent() {
    indentationTicks--;
  }
}

record SequenceD(Document Left, Document Right, Orientation Orientation) : Document {
  public void Render(int desiredWidth, IndentationWriter writer) {
    Left.Render(desiredWidth, writer);
    if (Orientation == Orientation.Adjacent) {
    } else if (Orientation == Orientation.Spaced) {
      if (!Left.IsEmpty && !Right.IsEmpty) {
        writer.Write(" ");
      }
    } else if (Orientation == Orientation.Vertical || Orientation == Orientation.LineBroken) {
      if (Orientation == Orientation.LineBroken) {
        writer.WriteLine();
      }
      writer.WriteLine();
    } else if (Orientation == Orientation.SpacedOrVertical) {
      throw new NotImplementedException();
      // if (writer.LineWidth + Right.Width > desiredWidth) {
      //   writer.WriteLine();
      // }
    } else {
      throw new NotSupportedException();
    }
    Right.Render(desiredWidth, writer);
  }

  public bool IsEmpty => Left.IsEmpty && Right.IsEmpty;
}