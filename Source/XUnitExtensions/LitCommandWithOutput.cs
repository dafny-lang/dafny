using System.IO;
using System.Text;

namespace XUnitExtensions {
  public class LitCommandWithOutput : ILitCommand {
    private ILitCommand command;
    private string inputFile;
    private string outputFile;
    private bool append;

    public LitCommandWithOutput(ILitCommand command, string inputFile, string outputFile, bool append) {
      this.command = command;
      this.inputFile = inputFile;
      this.outputFile = outputFile;
      this.append = append;
    }

    public (int, string, string) Execute(TextReader inReader, TextWriter outWriter) {
      var inputReader = inputFile != null ? new StreamReader(inputFile) : null;
      var outputWriter = outputFile != null ? new StreamWriter(outputFile, append) : null;
      return command.Execute(inputReader, outputWriter);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(command);
      if (outputFile != null) {
        builder.Append(append ? " >> " : " > ");
        builder.Append(outputFile);
      }
      return builder.ToString();
    }
  }
}