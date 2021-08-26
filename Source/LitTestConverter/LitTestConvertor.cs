using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyDriver.Test;
using DafnyDriver.Test.XUnitExtensions;
using YamlDotNet.Serialization;
using YamlDotNet.Serialization.NamingConventions;

namespace LitTestConvertor {
  
  public class LitTestConvertor {

    private const string DAFNY_COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";
    private const string LIT_DAFNY = "%dafny";
    private const string LIT_SERVER = "%server";
    
    // Fake options for which files are passed to the CLI
    public const string TEST_CONFIG_OTHER_FILES = "otherFiles";
    public const string TEST_CONFIG_INCLUDE_THIS_FILE = "includeThisFile";
    
    // Arguments that are taken care of automatically. If a test is actually using the output of
    // one of these as input in another command, that will be flagged as an unsupported
    // use of lit substitution.
    private static readonly string[] DAFNY_IGNORED_OPTIONS = {
      "print",
      "dprint",
      "rprint"
    };
    
    private int count = 0;
    private int verifyOnlyCount = 0;
    private int defaultCount = 0;
    private int alreadyConverted = 0;
    private int invalidCount = 0;

    public void ConvertLitTest(string filePath) {
      IEnumerable<CLITestCase> testSpec;
      IEnumerable<string> testContent;
      if (filePath.Contains("/Inputs/")) {
        testSpec = Enumerable.Empty<CLITestCase>();
        testContent = File.ReadAllLines(filePath);
      } else {
        (testSpec, testContent) = ConvertLitCommands(filePath, File.ReadAllLines(filePath));
      }
      
      ISerializer serializer = new SerializerBuilder()
        .WithNamingConvention(CamelCaseNamingConvention.Instance)
        .ConfigureDefaultValuesHandling(DefaultValuesHandling.OmitDefaults)
        .WithTagMapping("!dafnyTestSpec", typeof(DafnyTestSpec))
        .WithTagMapping("!foreach", typeof(ForEachArgumentList))
        .Build();
      
      using (StreamWriter file = new StreamWriter(filePath)) {
        if (testSpec != null) {
          file.WriteLine("/*");
          file.WriteLine("---");
          serializer.Serialize(file, testSpec);
          file.WriteLine("*/");
        }
        foreach (var line in testContent) {
          file.WriteLine(line);
        }
      }
    }

    public (IEnumerable<CLITestCase> spec, IEnumerable<string> content) ConvertLitCommands(string filePath, IEnumerable<string> lines) {
      var litCommands = lines.Select(ExtractLitCommand).TakeWhile(c => c != null).ToList();
      if (!litCommands.Any()) {
        throw new ArgumentException("No lit commands found");
      }
      
      // Make sure the commands are consecutive
      var testContent = lines.Skip(litCommands.Count);
      if (testContent.Any(line => ExtractLitCommand(line) != null)) {
        throw new ArgumentException("Lit commands are not consecutive");
      }

      if (litCommands.Count == 1 && litCommands.Single().StartsWith("echo")) {
        // This is an idiom for Dafny files used elsewhere
        return (Enumerable.Empty<CLITestCase>(), testContent);
      }

      if (!litCommands[^1].Equals("%diff \"%s.expect\" \"%t\"")) {
        throw new ArgumentException("Last lit command is not expected %diff: " + litCommands[^1]);
      }
      litCommands.RemoveAt(litCommands.Count - 1);
      
      List<CLITestCase> testConfigs = litCommands.Select(c => ParseDafnyCommandArguments(filePath, c)).ToList();

      if (testConfigs.Count == 1) {
        var single = testConfigs.Single();
        if (IsStandardVerifyOnly(single)) {
          verifyOnlyCount++;
        }
        return (single, testContent);
      } 
      
      if (IsStandardVerifyOnly(testConfigs[0]) && testConfigs.Skip(1).All(IsStandardCompileAndRun)
            || testConfigs.Skip(1).All(IsStandardCompileAndRun)) {
        defaultCount++;
        // TODO: For now don't return a value, since we also have to split up the .expect
        // files for this to work.
        // return (null, testContent);
        throw new ArgumentException("Default for-each-compiler test cases not yet supported");
      }
      
      throw new ArgumentException("Multi-command lit tests require manual conversion");
    }
    
    private static bool IsStandardCompileAndRun(DafnyTestSpec spec) {
      
      return spec.CompileTarget != null &&
             ((spec.Compile == 3 && spec.DafnyArguments.Count == 2) ||
              // /compile:4 might be used with /noVerify
              (spec.Compile == 4 && spec.DafnyArguments.Count <= 3));
    }
    
    private static bool IsStandardVerifyOnly(DafnyTestSpec spec) {
      return spec.Compile == 0 && spec.DafnyArguments.Count == 1;
    }
    
    private static string ExtractLitCommand(string line) {
      if (!line.StartsWith(DAFNY_COMMENT_PREFIX)) {
        return null;
      }
      line = line.Substring(DAFNY_COMMENT_PREFIX.Length).Trim();

      if (!line.StartsWith(LIT_COMMAND_PREFIX)) {
        return null;
      }
      return line.Substring(LIT_COMMAND_PREFIX.Length).Trim();
    }
        
    private CLITestCase ParseDafnyCommandArguments(string filePath, string dafnyCommand) {
      bool includeThisFile = true;
      List<string> otherFiles = new();
      Dictionary<string, string> dafnyArguments = new();
      
      if (!dafnyCommand.StartsWith(LIT_DAFNY)) {
        throw new ArgumentException("Lit command is not expected %dafny: " + dafnyCommand);
      }

      string argumentsString = dafnyCommand.Substring(LIT_DAFNY.Length);
      var arguments = argumentsString.Split((char[])null, StringSplitOptions.RemoveEmptyEntries).ToList();
      
      // Ensure the last two parts are > "%t" or >> "%t"
      if (arguments.Count < 3) {
        throw new ArgumentException("Not enough arguments to %dafny command: " + dafnyCommand);
      }
      if (!arguments[^1].Equals("\"%t\"") 
          || !(arguments[^2].Equals(">") || arguments[^2].Equals(">>")))
      {
        throw new ArgumentException("Non-standard output in %dafny command: " + dafnyCommand);
      }
      arguments.RemoveRange(arguments.Count - 2, 2);

      if (!arguments.Remove("\"%s\"")) {
        includeThisFile = false;
      }
      
      // Check the arguments for anything non-standard
      foreach (var argument in arguments) {
        var (key, value) = ParseDafnyArgument(argument);
        if (DAFNY_IGNORED_OPTIONS.Contains(key)) {
          continue;
        }
        if (value.Contains("%")) {
          throw new ArgumentException("Use of lit substitution (% variable) requires manual conversion: " + argument);
        }
        if (key.Equals(TEST_CONFIG_OTHER_FILES)) {
          otherFiles.Add(value);
        } else {
          dafnyArguments.Add(key, value);
        }
      }

      return new DafnyTestCase();
    }

    private static (string, string) ParseDafnyArgument(string argument) {
      if (argument.StartsWith("-") || argument.StartsWith("/")) {
        argument = argument[1..];
        int colonIndex = argument.IndexOf(":");
        if (colonIndex >= 0) {
          return (argument[..colonIndex], argument[(colonIndex + 1)..]);
        } else {
          return (argument, "yes");
        }
      } else {
        return (TEST_CONFIG_OTHER_FILES, argument);
      }
    }

    public void Run(string root) {
      // TODO-RS: Search for "*.transcript" too
      if (!Directory.Exists(root)) {
        ConvertLitTest(root);
        return;
      }
      foreach (var file in Directory.GetFiles(root, "*.dfy", SearchOption.AllDirectories)) {
        try {
          count++;
          ConvertLitTest(file);
        } catch (ArgumentException e) {
          invalidCount++;
          Console.WriteLine(file + ": " + e.Message);
        }
      }
      
      Console.WriteLine("");
      Console.WriteLine("Already converted: " + alreadyConverted + "/" + count);
      Console.WriteLine("Default: " + defaultCount + "/" + count);
      Console.WriteLine("Verify only: " + verifyOnlyCount + "/" + count);
      Console.WriteLine("Invalid: " + invalidCount + "/" + count);
    }

    public static void Main(string[] args) { 
      new LitTestConvertor().Run(args[0]);
    }
  }
}