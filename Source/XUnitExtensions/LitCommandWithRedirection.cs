using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace XUnitExtensions {
  public class LitCommandWithRedirection : ILitCommand {

    public static LitCommandWithRedirection Parse(string[] tokens, LitTestConfiguration config) {
      var commandSymbol = tokens[0];
      var (rawArguments, inputFile, outputFile, appendOutput) = ExtractRedirections(tokens[1..]);
      if (inputFile != null) {
        inputFile = config.ApplySubstitutions(inputFile);
      }
      if (outputFile != null) {
        outputFile = config.ApplySubstitutions(outputFile);
      }

      var arguments = rawArguments.Select(config.ApplySubstitutions);
      
      if (config.Commands.TryGetValue(commandSymbol, out var command)) {
        return new LitCommandWithRedirection(command(arguments, config), inputFile, outputFile, appendOutput);
      }

      commandSymbol = config.ApplySubstitutions(commandSymbol);

      return new LitCommandWithRedirection(
        new ShellLitCommand(commandSymbol, arguments, config.PassthroughEnvironmentVariables), 
        inputFile, outputFile, appendOutput);
    }
    
    public static (IEnumerable<string>, string, string, bool) ExtractRedirections(IEnumerable<string> arguments) {
      var argumentsList = arguments.ToList();
      string inputFile = null;
      string outputFile = null;
      bool appendOutput = false;
      var redirectInIndex = argumentsList.IndexOf("<");
      if (redirectInIndex >= 0) {
        inputFile = argumentsList[redirectInIndex + 1];
        argumentsList.RemoveRange(redirectInIndex, 2);
      }
      var redirectOutIndex = argumentsList.IndexOf(">");
      if (redirectOutIndex >= 0) {
        outputFile = argumentsList[redirectOutIndex + 1];
        argumentsList.RemoveRange(redirectOutIndex, 2);
      }
      var redirectAppendIndex = argumentsList.IndexOf(">>");
      if (redirectAppendIndex >= 0) {
        outputFile = argumentsList[redirectAppendIndex + 1];
        appendOutput = true;
        argumentsList.RemoveRange(redirectAppendIndex, 2);
      }
      return (argumentsList, inputFile, outputFile, appendOutput);
    }
    
    private ILitCommand command;
    private string inputFile;
    private string outputFile;
    private bool append;

    public LitCommandWithRedirection(ILitCommand command, string inputFile, string outputFile, bool append) {
      this.command = command;
      this.inputFile = inputFile;
      this.outputFile = outputFile;
      this.append = append;
    }

    public (int, string, string) Execute(TextReader inReader, TextWriter outWriter) {
      var inputReader = inputFile != null ? new StreamReader(inputFile) : null;
      var outputWriter = outputFile != null ? new StreamWriter(outputFile, append) : null;
      return command.Execute(inputReader, outputWriter);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(command);
      if (outputFile != null) {
        builder.Append(append ? " >> " : " > ");
        builder.Append(outputFile);
      }
      return builder.ToString();
    }
  }
}