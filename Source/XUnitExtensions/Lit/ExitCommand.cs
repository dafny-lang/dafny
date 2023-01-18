using System.IO;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit; 

public class ExitCommand : ILitCommand {
  private readonly int expectedExitCode;
  private readonly ILitCommand operand;

  public ExitCommand(int exitCode, ILitCommand operand) {
    this.expectedExitCode = exitCode;
    this.operand = operand;
  }

  public (int, string, string) Execute(ITestOutputHelper? outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
    var (exitCode, output, error) = operand.Execute(outputHelper, inputReader, outputWriter, errorWriter);
    if (exitCode == expectedExitCode) {
      return (0, output, error);
    } else {
      return (1, output, error + $"\nMoreover the expected exit code was {expectedExitCode} but got {exitCode}");
    }
  }

  public override string ToString() {
    return $"%exit {expectedExitCode}  {operand}";
  }
}
