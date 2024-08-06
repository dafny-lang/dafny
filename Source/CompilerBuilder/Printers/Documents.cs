namespace CompilerBuilder;

public interface Document {
  
}

record Verbatim(string Value) : Document;
record Empty : Document;

public enum Orientation {
  Horizontal,
  Vertical
};

record SequenceD(Document Left, Document Right, Orientation Orientation) : Document;