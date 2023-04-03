using System.IO;
using System.Threading;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit; 

public class StdInCommand : ILitCommand {
  private readonly string stdin;
  private readonly ILitCommand operand;

  public StdInCommand(string stdin, ILitCommand operand) {
    this.stdin = stdin.Replace("\\n", "\n");
    this.operand = operand;
  }

  public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader,
    TextWriter? outputWriter, TextWriter? errorWriter) {
    inputReader = new StringReader(stdin);
    return operand.Execute(outputHelper, inputReader, outputWriter, errorWriter);
  }

  public override string ToString() {
    return $"%stdin \"{stdin.Replace("\n", "\\n")}\"  {operand}";
  }
}
