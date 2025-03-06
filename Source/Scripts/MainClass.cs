using System.CommandLine;
using IntegrationTests;

namespace Scripts;

public class MainClass {
  public static Task Main(string[] args) {
    var root = new RootCommand("Various scripts that help develop Dafny");
    root.AddCommand(UpdateTests.GetCommand());
    root.AddCommand(SyntaxSchemaGenerator.GetCommand());
    root.AddCommand(SyntaxDeserializerGenerator.GetCommand());
    root.AddCommand(SourceToBinary.GetCommand());
    return root.InvokeAsync(args);
  }
}