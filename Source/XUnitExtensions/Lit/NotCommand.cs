using System.IO;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit;

public class NotCommand : ILitCommand {
  private readonly ILitCommand operand;

  public NotCommand(ILitCommand operand) {
    this.operand = operand;
  }

  public async Task<(int, string, string)> Execute(TextReader inputReader,
    TextWriter outputWriter, TextWriter errorWriter) {
    var (exitCode, output, error) = await operand.Execute(inputReader, outputWriter, errorWriter);
    return (exitCode == 0 ? 1 : 0, output, error);
  }

  public override string ToString() {
    return $"! {operand}";
  }
}