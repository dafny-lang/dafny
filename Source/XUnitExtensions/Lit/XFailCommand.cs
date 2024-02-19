using System;
using System.IO;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class XFailCommand : ILitCommand {

    public static ILitCommand Parse(string line, LitTestConfiguration config) {
      // Only supporting * for now
      if (line.Equals("*")) {
        return new XFailCommand();
      }

      throw new ArgumentException($"Unrecognized arguments to XFAIL: {line}");
    }

    public Task<int> Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      return Task.FromResult(0);
    }
  }
}