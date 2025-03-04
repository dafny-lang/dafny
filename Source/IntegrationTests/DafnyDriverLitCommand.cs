using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using XUnitExtensions.Lit;

namespace IntegrationTests;

delegate Task<int> MainWithWriters(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args);

class MainWithWritersCommand : ILitCommand {
  private readonly string name;
  private readonly MainWithWriters main;
  public string[] Arguments { get; }

  public MainWithWritersCommand(string name, IEnumerable<string> arguments, MainWithWriters main) {
    this.name = name;
    this.main = main;
    Arguments = arguments.ToArray();
  }

  public Task<int> Execute(TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter) {
    return main(outputWriter, errorWriter, inputReader, Arguments);
  }

  public override string ToString() {
    return $"{name} {string.Join(" ", Arguments)}";
  }
}