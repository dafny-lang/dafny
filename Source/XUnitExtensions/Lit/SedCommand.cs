using System;
using System.IO;
using System.Text.RegularExpressions;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions.Lit {
  public class SedCommand : ILitCommand {

    private readonly string regexp;
    private readonly string replaceBy;
    private readonly string file;

    const string SupportedRegexReplace = @"s/((?:\\/|[^/])+)/((?:[^/]|\\/)*)/";

    private SedCommand(string regexp, string replaceBy, string file) {
      this.regexp = regexp;
      this.replaceBy = replaceBy;
      this.file = file;
    }

    public static ILitCommand Parse(string[] args) {
      if (args.Length != 2) {
        throw new ArgumentException($"Wrong number of arguments for sed: {args.Length}");
      }
      var regexpReplace = args[0];

      var parseRegex = new Regex(SupportedRegexReplace);
      var match = parseRegex.Match(regexpReplace);
      if (match == null) {
        throw new NotImplementedException("No support for sed " + regexpReplace + ". Only support for " +
                                          SupportedRegexReplace);
      }
      var regexp = match.Groups[1].Value;
      var replaceBy = match.Groups[2].Value;
      var file = args[1];
      return new SedCommand(regexp, replaceBy, file);
    }

    public (int, string, string) Execute(TextReader? inputReader,
      TextWriter? outputWriter, TextWriter? errorWriter) {
      var fileContent = File.ReadAllText(file);
      try {
        var stdOutput = Regex.Replace(fileContent, "(?m)" + regexp, replaceBy);
        if (outputWriter != null) {
          outputWriter.Write(stdOutput);
        }
        return (0, stdOutput, "");
      } catch (Exception e) {
        return (1, e.ToString(), "");
      }
    }

    public override string ToString() {
      return $"sedCommand {regexp} {replaceBy} {file}";
    }
  }
}
