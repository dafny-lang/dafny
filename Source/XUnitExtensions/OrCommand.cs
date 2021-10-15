using System.IO;

namespace XUnitExtensions {
  public class OrCommand : ILitCommand {
    private readonly ILitCommand lhs;
    private readonly ILitCommand rhs;

    public OrCommand(ILitCommand lhs, ILitCommand rhs) {
      this.lhs = lhs;
      this.rhs = rhs;
    }
    
    public (int, string, string) Execute(TextReader inputReader, TextWriter outputWriter) {
      var (exitCode, output, error) = lhs.Execute(inputReader, outputWriter);
      if (exitCode == 0) {
        return (exitCode, output, error);
      } else {
        return rhs.Execute(inputReader, outputWriter);
      }
    }
  }
}