using System.IO;

namespace XUnitExtensions {
  public class OrCommand : ILitCommand {
    private readonly ILitCommand lhs;
    private readonly ILitCommand rhs;

    public OrCommand(ILitCommand lhs, ILitCommand rhs) {
      this.lhs = lhs;
      this.rhs = rhs;
    }

    public (int, string, string) Execute(TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter) {
      var (exitCode, output, error) = lhs.Execute(inputReader, outputWriter, errorWriter);
      if (exitCode == 0) {
        return (exitCode, output, error);
      }
      return rhs.Execute(inputReader, outputWriter, errorWriter);
    }

    public override string ToString() {
      return $"{lhs} || {rhs}";
    }
  }
}