using System.IO;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class OrCommand : ILitCommand {
    private readonly ILitCommand lhs;
    private readonly ILitCommand rhs;

    public OrCommand(ILitCommand lhs, ILitCommand rhs) {
      this.lhs = lhs;
      this.rhs = rhs;
    }

    public async Task<(int, string, string)> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      var (leftExitCode, leftOutput, leftError) = await lhs.Execute(inputReader, outputWriter, errorWriter);
      if (leftExitCode == 0) {
        return (leftExitCode, leftOutput, leftError);
      }

      var (rightExitCode, rightOutput, rightError) = await rhs.Execute(inputReader, outputWriter, errorWriter);
      return (rightExitCode, leftOutput + rightOutput, leftError + rightError);
    }

    public override string ToString() {
      return $"{lhs} || {rhs}";
    }
  }
}