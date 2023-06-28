using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class LitCommandWithRedirection : ILitCommand {

    public static LitCommandWithRedirection Parse(Token[] tokens, LitTestConfiguration config) {
      var commandSymbol = tokens[0].Value;
      var argumentList = tokens[1..].ToList();
      string? inputFile = null;
      string? outputFile = null;
      var appendOutput = false;
      string? errorFile = null;
      var redirectInIndex = argumentList.FindIndex(t => t.Value == "<");
      if (redirectInIndex >= 0) {
        inputFile = config.ApplySubstitutions(argumentList[redirectInIndex + 1].Value).Single();
        argumentList.RemoveRange(redirectInIndex, 2);
      }
      var redirectOutIndex = argumentList.FindIndex(t => t.Value == ">");
      if (redirectOutIndex >= 0) {
        outputFile = config.ApplySubstitutions(argumentList[redirectOutIndex + 1].Value).Single();
        argumentList.RemoveRange(redirectOutIndex, 2);
      }
      var redirectAppendIndex = argumentList.FindIndex(t => t.Value == ">>");
      if (redirectAppendIndex >= 0) {
        outputFile = config.ApplySubstitutions(argumentList[redirectAppendIndex + 1].Value).Single();
        appendOutput = true;
        argumentList.RemoveRange(redirectAppendIndex, 2);
      }
      var redirectErrorIndex = argumentList.FindIndex(t => t.Value == "2>");
      if (redirectErrorIndex >= 0) {
        errorFile = config.ApplySubstitutions(argumentList[redirectErrorIndex + 1].Value).Single();
        argumentList.RemoveRange(redirectErrorIndex, 2);
      }
      var redirectErrorAppendIndex = argumentList.FindIndex(t => t.Value == "2>>");
      if (redirectErrorAppendIndex >= 0) {
        errorFile = config.ApplySubstitutions(argumentList[redirectErrorAppendIndex + 1].Value).Single();
        appendOutput = true;
        argumentList.RemoveRange(redirectErrorAppendIndex, 2);
      }

      ILitCommand CreateCommand() {
        var arguments = argumentList.SelectMany(a => config.ApplySubstitutions(a.Value).Select(v => a with { Value = v }))
          .ToList()
          .SelectMany(a => a.Kind == Kind.MustGlob ? ExpandGlobs(a.Value) : new[] { a.Value })
          .ToList();
        if (config.Commands.TryGetValue(commandSymbol, out var command)) {
          return command(arguments, config);
        }

        commandSymbol = config.ApplySubstitutions(commandSymbol).Single();
        return new ShellLitCommand(commandSymbol, arguments, config.PassthroughEnvironmentVariables);
      }

      // Use a DelayedLitCommand so the glob expansion is done only after previous commands have executed
      return new LitCommandWithRedirection(new DelayedLitCommand(CreateCommand), inputFile, outputFile, appendOutput, errorFile);
    }

    public ILitCommand Command;
    public string? InputFile;
    public string? OutputFile;
    public bool Append;
    public string? ErrorFile;

    public LitCommandWithRedirection(ILitCommand command, string? inputFile, string? outputFile, bool append, string? errorFile) {
      this.Command = command;
      this.InputFile = inputFile;
      this.OutputFile = outputFile;
      this.Append = append;
      this.ErrorFile = errorFile;
    }

    public (int, string, string) Execute(TextReader inputReader, TextWriter outWriter, TextWriter errWriter) {
      var outputWriters = new List<TextWriter> { outWriter };
      if (OutputFile != null) {
        outputWriters.Add(new StreamWriter(OutputFile, Append));
      }
      inputReader = InputFile != null ? new StreamReader(InputFile) : inputReader;

      var errorWriters = new List<TextWriter> { errWriter };
      if (ErrorFile != null) {
        errorWriters.Add(new StreamWriter(ErrorFile, Append));
      }
      var result = Command.Execute(inputReader,
        new CombinedWriter(outWriter.Encoding, outputWriters),
        new CombinedWriter(errWriter.Encoding, errorWriters));
      inputReader.Close();
      foreach (var writer in outputWriters.Concat(errorWriters)) {
        writer.Close();
      }
      return result;
    }

    protected static IEnumerable<string> ExpandGlobs(string chunk) {
      var matcher = new Matcher();
      var root = Path.GetPathRoot(chunk)!;
      var rest = Path.GetRelativePath(root, chunk);
      matcher.AddInclude(rest);
      var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(root)));
      return result.Files.Select(f => Path.Combine(root, f.Path));
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(Command);
      if (InputFile != null) {
        builder.Append(" < ");
        builder.Append(InputFile);
      }
      if (OutputFile != null) {
        builder.Append(Append ? " >> " : " > ");
        builder.Append(OutputFile);
      }
      if (ErrorFile != null) {
        builder.Append(" 2> ");
        builder.Append(ErrorFile);
      }
      return builder.ToString();
    }
  }
}