namespace CompilerBuilder;

public interface IPosition {
  int Offset { get; }
  int Line { get; }
  int Column { get; }
}

public record ParseRange(IPosition From, IPosition Until);

public interface ITextPointer : IPosition {

  bool SeenHere(Parser parser);
  ITextPointer Add(Parser parser);
  ITextPointer Remove(Parser parser);
  
  ITextPointer Drop(int amount);

  string LocationDescription => Length == 0 ? "end of text" : SubSequence(5).ToString();
  
  char First { get; }
  int Length { get; }
  char At(int offset);
  
  ReadOnlySpan<char> Remainder { get; }
  ReadOnlySpan<char> SubSequence(int length);

  FailureResult<T> Fail<T>(string expected) {
    return new FailureResult<T>($"'{LocationDescription}' is not {expected}", this);
  }
}