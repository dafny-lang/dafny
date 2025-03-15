namespace Microsoft.Dafny;

public class SimpleLocation {
  public int StartLine { get; }
  public int StartCharacter { get; }
  public int EndLine { get; }
  public int EndCharacter { get; }

  public SimpleLocation(int startLine, int startCharacter, int endLine, int endCharacter) {
    StartLine = startLine;
    StartCharacter = startCharacter;
    EndLine = endLine;
    EndCharacter = endCharacter;
  }
}