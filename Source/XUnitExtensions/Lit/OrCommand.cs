using System.IO;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class OrCommand(ILitCommand lhs, ILitCommand rhs) : ILitCommand {
    public async Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      var leftExitCode = await lhs.Execute(inputReader, outputWriter, errorWriter);
      if (leftExitCode == 0) {
        return leftExitCode;
      }

      var rightExitCode = await rhs.Execute(inputReader, outputWriter, errorWriter);
      return rightExitCode;
    }

    public override string ToString() {
      return $"{lhs} || {rhs}";
    }
  }
}