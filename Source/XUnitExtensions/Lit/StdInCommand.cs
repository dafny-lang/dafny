using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit;

public class StdInCommand : ILitCommand {
  private readonly string stdin;
  private readonly ILitCommand operand;

  public StdInCommand(string stdin, ILitCommand operand) {
    this.stdin = stdin.Replace("\\n", "\n");
    this.operand = operand;
  }

  public Task<int> Execute(TextReader inputReader,
    TextWriter outputWriter, TextWriter errorWriter) {
    inputReader = new StringReader(stdin);
    return operand.Execute(inputReader, outputWriter, errorWriter);
  }

  public override string ToString() {
    return $"%stdin \"{stdin.Replace("\n", "\\n")}\"  {operand}";
  }
}
