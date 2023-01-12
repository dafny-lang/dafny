using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class LitCommandWithRedirection : ILitCommand {

    public static LitCommandWithRedirection Parse(string[] tokens, LitTestConfiguration config) {
      var commandSymbol = tokens[0];
      var argumentsList = tokens[1..].ToList();
      string? inputFile = null;
      string? outputFile = null;
      var appendOutput = false;
      string? errorFile = null;
      var redirectInIndex = argumentsList.IndexOf("<");
      if (redirectInIndex >= 0) {
        inputFile = config.ApplySubstitutions(argumentsList[redirectInIndex + 1]).Single();
        argumentsList.RemoveRange(redirectInIndex, 2);
      }
      var redirectOutIndex = argumentsList.IndexOf(">");
      if (redirectOutIndex >= 0) {
        outputFile = config.ApplySubstitutions(argumentsList[redirectOutIndex + 1]).Single();
        argumentsList.RemoveRange(redirectOutIndex, 2);
      }
      var redirectAppendIndex = argumentsList.IndexOf(">>");
      if (redirectAppendIndex >= 0) {
        outputFile = config.ApplySubstitutions(argumentsList[redirectAppendIndex + 1]).Single();
        appendOutput = true;
        argumentsList.RemoveRange(redirectAppendIndex, 2);
      }
      var redirectErrorIndex = argumentsList.IndexOf("2>");
      if (redirectErrorIndex >= 0) {
        errorFile = config.ApplySubstitutions(argumentsList[redirectErrorIndex + 1]).Single();
        argumentsList.RemoveRange(redirectErrorIndex, 2);
      }
      var redirectErrorAppendIndex = argumentsList.IndexOf("2>>");
      if (redirectErrorAppendIndex >= 0) {
        errorFile = config.ApplySubstitutions(argumentsList[redirectErrorAppendIndex + 1]).Single();
        appendOutput = true;
        argumentsList.RemoveRange(redirectErrorIndex, 2);
      }

      var arguments = argumentsList.SelectMany(config.ApplySubstitutions);

      if (config.Commands.TryGetValue(commandSymbol, out var command)) {
        return new LitCommandWithRedirection(command(arguments, config), inputFile, outputFile, appendOutput, errorFile);
      }

      commandSymbol = config.ApplySubstitutions(commandSymbol).Single();

      return new LitCommandWithRedirection(
        new ShellLitCommand(commandSymbol, arguments, config.PassthroughEnvironmentVariables),
        inputFile, outputFile, appendOutput, errorFile);
    }

    private readonly ILitCommand command;
    private readonly string? inputFile;
    private readonly string? outputFile;
    private readonly bool append;
    private readonly string? errorFile;

    public LitCommandWithRedirection(ILitCommand command, string? inputFile, string? outputFile, bool append, string? errorFile) {
      this.command = command;
      this.inputFile = inputFile;
      this.outputFile = outputFile;
      this.append = append;
      this.errorFile = errorFile;
    }

    public (int, string, string) Execute(ITestOutputHelper? outputHelper, TextReader? inReader, TextWriter? outWriter, TextWriter? errWriter) {
      var inputReader = inputFile != null ? new StreamReader(inputFile) : null;
      var outputWriter = outputFile != null ? new StreamWriter(outputFile, append) : null;
      var errorWriter = errorFile != null ? new StreamWriter(errorFile, false) : null;
      var result = command.Execute(outputHelper, inputReader, outputWriter, errorWriter);
      inputReader?.Close();
      outputWriter?.Close();
      errorWriter?.Close();
      return result;
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(command);
      if (inputFile != null) {
        builder.Append(" < ");
        builder.Append(inputFile);
      }
      if (outputFile != null) {
        builder.Append(append ? " >> " : " > ");
        builder.Append(outputFile);
      }
      if (errorFile != null) {
        builder.Append(" 2> ");
        builder.Append(errorFile);
      }
      return builder.ToString();
    }
  }
}
