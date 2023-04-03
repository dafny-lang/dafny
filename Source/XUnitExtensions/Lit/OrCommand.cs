using System.IO;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class OrCommand : ILitCommand {
    private readonly ILitCommand lhs;
    private readonly ILitCommand rhs;

    public OrCommand(ILitCommand lhs, ILitCommand rhs) {
      this.lhs = lhs;
      this.rhs = rhs;
    }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader,
      TextWriter? outputWriter, TextWriter? errorWriter) {
      var (leftExitCode, leftOutput, leftError) = lhs.Execute(outputHelper, inputReader, outputWriter, errorWriter);
      if (leftExitCode == 0) {
        return (leftExitCode, leftOutput, leftError);
      }

      var (rightExitCode, rightOutput, rightError) = rhs.Execute(outputHelper, inputReader, outputWriter, errorWriter);
      return (rightExitCode, leftOutput + rightOutput, leftError + rightError);
    }

    public override string ToString() {
      return $"{lhs} || {rhs}";
    }
  }
}