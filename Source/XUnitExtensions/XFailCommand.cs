using System.IO;

namespace XUnitExtensions {
  public class XFailCommand : ILitCommand {

    public XFailCommand() { }

    public (int, string, string) Execute(TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter) {
      return (0, "", "");
    }
  }
}