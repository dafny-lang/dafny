using System.IO;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit;

public class NotCommand(ILitCommand operand) : ILitCommand {
  public async Task<int> Execute(TextReader inputReader,
    TextWriter outputWriter, TextWriter errorWriter) {
    var exitCode = await operand.Execute(inputReader, outputWriter, errorWriter);
    return exitCode == 0 ? 1 : 0;
  }

  public override string ToString() {
    return $"! {operand}";
  }
}