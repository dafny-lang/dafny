using System.IO;
using System.Text;

namespace XUnitExtensions {
  public class LitCommandWithOutput {
    private ILitCommand command;
    private string outputFile;
    private bool append;

    public LitCommandWithOutput(ILitCommand command, string outputFile, bool append) {
      this.command = command;
      this.outputFile = outputFile;
      this.append = append;
    }

    public (int, string, string) Execute() {
      var outputWriter = outputFile != null ? new StreamWriter(outputFile, append) : null;
      return command.Execute(outputWriter);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(command);
      if (outputFile != null) {
        builder.Append(append ? " >> " : ">");
        builder.Append(outputFile);
      }
      return builder.ToString();
    }
  }
}