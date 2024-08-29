using System.ComponentModel;
using System.IO;
using System.Threading.Tasks;

namespace XUnitExtensions.Lit;


public class ExitCommand : ILitCommand {
  private readonly string expectedExitCode;
  private readonly ILitCommand operand;

  public ExitCommand(string exitCode, ILitCommand operand) {
    this.expectedExitCode = exitCode;
    this.operand = operand;
  }

  public async Task<int> Execute(TextReader inputReader,
    TextWriter outputWriter, TextWriter errorWriter) {
    var exitCode = 1;
    try {
      exitCode = await operand.Execute(inputReader, outputWriter, errorWriter);
    } catch (Win32Exception) {
      if (expectedExitCode == "-any") {
      } else {
        throw;
      }
    }

    if (expectedExitCode == "-any" || exitCode.ToString() == expectedExitCode) {
      return 0;
    }

    await errorWriter.WriteLineAsync($"Moreover the expected exit code was {expectedExitCode} but got {exitCode}");
    return 1;
  }

  public override string ToString() {
    return $"%exits-with {expectedExitCode}  {operand}";
  }
}
