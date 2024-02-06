using System.IO;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit;

public class ExitCommand : ILitCommand {
  private readonly int expectedExitCode;
  private readonly ILitCommand operand;

  public ExitCommand(int exitCode, ILitCommand operand) {
    this.expectedExitCode = exitCode;
    this.operand = operand;
  }

  public async Task<int> Execute(TextReader inputReader,
    TextWriter outputWriter, TextWriter errorWriter) {
    var exitCode = await operand.Execute(inputReader, outputWriter, errorWriter);
    if (exitCode == expectedExitCode) {
      return 0;
    }

    await errorWriter.WriteLineAsync($"Moreover the expected exit code was {expectedExitCode} but got {exitCode}");
    return 1;
  }

  public override string ToString() {
    return $"%exits-with {expectedExitCode}  {operand}";
  }
}
