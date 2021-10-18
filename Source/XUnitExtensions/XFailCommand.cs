using System.IO;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public class XFailCommand : ILitCommand {

    public XFailCommand() { }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      return (0, "", "");
    }
  }
}