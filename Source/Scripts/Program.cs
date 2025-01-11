using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Parsing;

namespace IntegrationTests;

public class Program {
  public static Task Main(string[] args) {
    var root = new RootCommand("Various scripts that help develop Dafny");
    root.AddCommand(UpdateTests.GetCommand());
    return root.InvokeAsync(args);
  }
}