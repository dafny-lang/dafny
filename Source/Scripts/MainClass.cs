using System.CommandLine;
using System.CommandLine.Builder;
using System.CommandLine.Parsing;

namespace IntegrationTests;

public class MainClass {
  public static Task Main(string[] args) {
    var root = new RootCommand("Various scripts that help develop Dafny");
    root.AddCommand(UpdateTests.GetCommand());
    root.AddCommand(ParsedAstGenerator.GetCommand());
    root.AddCommand(DeserializerGenerator.GetCommand());
    return root.InvokeAsync(args);
  }
}