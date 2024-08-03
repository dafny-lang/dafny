namespace CompilerBuilder;

public interface IPosition {
  int Offset { get; }
  int Line { get; }
  int Column { get; }
}

public record ParseRange(IPosition From, IPosition Until);

public interface ITextPointer : IPosition {

  ITextPointer Drop(int amount);
  
  char First { get; }
  int Length { get; }
  char At(int offset);
  string SubSequence(int length);
}