using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.AccessControl;
using System.Threading.Tasks;
using Microsoft.Dafny;
using XUnitExtensions.Lit;

namespace IntegrationTests;

delegate Task<int> MainWithWriters(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args);
class MainWithWritersCommand : ILitCommand {
  private readonly MainWithWriters main;
  public string[] Arguments { get; }


  public MainWithWritersCommand(IEnumerable<string> arguments, MainWithWriters main) {
    this.main = main;
    Arguments = arguments.ToArray();
  }

  public Task<int> Execute(TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter) {
    return main(outputWriter, errorWriter, inputReader, Arguments);
  }
}

// TODO replace with MainWithWritersCommand
class DafnyDriverLitCommand : ILitCommand {
  public string[] Arguments { get; }

  public DafnyDriverLitCommand(IEnumerable<string> arguments) {
    this.Arguments = arguments.ToArray();
  }

  public Task<int> Execute(TextReader inputReader,
    TextWriter outputWriter,
    TextWriter errorWriter) {
    return DafnyBackwardsCompatibleCli.MainWithWriters(outputWriter, errorWriter, inputReader, Arguments);
  }

  public override string ToString() {
    return $"dafny {string.Join(" ", Arguments)}";
  }
}