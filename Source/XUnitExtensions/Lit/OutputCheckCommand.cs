using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using CommandLine;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class OutputCheckOptions {
      
    [Value(0)]
    public string CheckFile { get; set; }
      
    [Option("file-to-check", Required = true, HelpText = "File to check")]
    public string FileToCheck { get; set; }
  }
  
  public readonly record struct OutputCheckCommand(OutputCheckOptions options) : ILitCommand {
    
    private abstract record CheckDirective(string File, int LineNumber) {
      
      private static readonly Dictionary<string, Func<string, int, string, CheckDirective>> DirectiveParsers = new();
      static CheckDirective() {
        DirectiveParsers.Add("CHECK:", CheckRegexp.Parse);
        DirectiveParsers.Add("CHECK-L:", CheckLiteral.Parse);
      }
      
      public static CheckDirective? Parse(string file, int lineNumber, string line) {
        foreach (var (keyword, parser) in DirectiveParsers) {
          var index = line.IndexOf(keyword);
          if (index >= 0) {
            var arguments = line[(index + keyword.Length)..].Trim();
            return parser(file, lineNumber, arguments);
          }
        }
        return null;
      }
      
      public abstract bool Matches(string line);
    }

    private record CheckRegexp(string File, int LineNumber, Regex Pattern) : CheckDirective(File, LineNumber) {
      public static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckRegexp(file, lineNumber, new Regex(arguments));
      }
      
      public override bool Matches(string line) {
        return Pattern.IsMatch(line);
      }

      public override string ToString() {
        return $"Check Directive ({File}:{LineNumber} Pattern: '{Pattern}')";
      }
    }
    
    private record CheckLiteral(string File, int LineNumber, string Literal) : CheckDirective(File, LineNumber) {
      public static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckLiteral(file, lineNumber, arguments);
      }
      
      public override bool Matches(string line) {
        return Literal == line.Trim();
      }
      
      public override string ToString() {
        return $"Check Directive ({File}:{LineNumber} Literal: '{Literal}')";
      }
    }
    
    public static ILitCommand Parse(IEnumerable<string> args, LitTestConfiguration config) {
      ILitCommand? result = null;
      Parser.Default.ParseArguments<OutputCheckOptions>(args).WithParsed(o => {
        result = new OutputCheckCommand(o);
      });
      return result!;
    }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader,
                                         TextWriter? outputWriter, TextWriter? errorWriter) {
      var linesToCheck = File.ReadAllLines(options.FileToCheck);
      var fileName = options.CheckFile;
      var checkDirectives = File.ReadAllLines(options.CheckFile)
        .Select((line, index) => CheckDirective.Parse(fileName, index + 1, line))
        .Where(e => e != null)
        .Select(e => e!)
        .ToList();
      
      if (checkDirectives.Any()) {
        int currentDirectiveIndex = 0;
        foreach (var lineToCheck in linesToCheck) {
          if (checkDirectives[currentDirectiveIndex].Matches(lineToCheck)) {
            currentDirectiveIndex++;
          }

          if (currentDirectiveIndex == checkDirectives.Count) {
            return (0, "", "");
          }
        }
        
        return (1, "", $"ERROR: Could not find a match for {checkDirectives[currentDirectiveIndex]}");
      } else {
        return (0, "", "");
      }
    }
  }
}