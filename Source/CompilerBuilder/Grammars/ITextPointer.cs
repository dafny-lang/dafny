namespace CompilerBuilder;

interface IPosition {
  int Offset { get; }
  int Line { get; }
  int Column { get; }
}

interface ITextPointer : IPosition {

  ITextPointer Drop(int amount);
  
  char First { get; }
  string SubSequence(int length);
}