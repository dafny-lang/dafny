using System.IO;

namespace XUnitExtensions {
  public class XFailCommand : ILitCommand {

    public XFailCommand() {}
    
    public (int, string, string) Execute(TextReader inputReader, TextWriter outputWriter) {
      return (0, "", "");
    }
  }
}