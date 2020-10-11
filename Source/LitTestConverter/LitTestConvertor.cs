using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace DafnyTests {
  
  public class LitTestConvertor {

    private const string DAFNY_COMMENT_PREFIX = "//";
    private const string LIT_COMMAND_PREFIX = "RUN:";
    private const string LIT_DAFNY = "%dafny";
    private const string LIT_SERVER = "%server";
    
    // Fake options to which files are passed to the CLI
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
    private int otherFilesCount = 0;
    private int invalidCount = 0;
        
    public void ConvertLitTest(string filePath) {
      if (filePath.Contains("/Inputs/")) {
        // TODO-RS: Need to add .common.yml file to disable Inputs/*.dfy
        return;
      }
      
      string[] lines = File.ReadAllLines(filePath);

      var litCommands = lines.Select(ExtractLitCommand).TakeWhile(c => c != null).ToList();
      // Make sure the commands are consecutive
      if (lines.Skip(litCommands.Count).Any(line => ExtractLitCommand(line) != null)) {
        throw new ArgumentException("Lit commands are not consecutive");
      }
      if (!litCommands.Any()) {
        return;
      }

      if (!litCommands[^1].Equals("%diff \"%s.expect\" \"%t\"")) {
        throw new ArgumentException("Last lit command is not expected %diff: " + litCommands[^1]);
      }
      litCommands.RemoveAt(litCommands.Count - 1);
      
      var testConfigs = litCommands.Select(ParseDafnyCommandArguments).ToList();

      if (testConfigs.Count == 1 && 
          testConfigs[0].Count == 1 && 
          DictionaryContainsEntry(testConfigs[0], DafnyTestSpec.DAFNY_COMPILE_OPTION, "0")) {
        verifyOnlyCount++;
        
      } else if (testConfigs.Count(c => c.ContainsKey(DafnyTestSpec.DAFNY_COMPILE_TARGET_OPTION)) > 1) {
        defaultCount++;
      }
    }

    private static bool DictionaryContainsEntry<K, V>(Dictionary<K, V> dictionary, K key, V value) {
      if (dictionary.TryGetValue(key, out var dictionaryValue)) {
        return value.Equals(dictionaryValue);
      } else {
        return false;
      }
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
        
    private Dictionary<string, string> ParseDafnyCommandArguments(string dafnyCommand) {
      var testConfig = new Dictionary<string, string>();
      var otherFiles = new List<string>();
      
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
        testConfig[TEST_CONFIG_INCLUDE_THIS_FILE] = "no";
      }
      
      // Check the arguments for anything non-standard
      foreach (var argument in arguments) {
        KeyValuePair<string, string> pair = ParseDafnyArgument(argument);
        if (DAFNY_IGNORED_OPTIONS.Contains(pair.Key)) {
          continue;
        }
        if (pair.Value.Contains("%")) {
          throw new ArgumentException("Use of lit substitution (% variable) requires manual conversion: " + argument);
        }
        if (pair.Key.Equals(TEST_CONFIG_OTHER_FILES)) {
          otherFiles.Add(pair.Value);
        } else {
          testConfig.Add(pair.Key, pair.Value);
        }
      }

      if (otherFiles.Any()) {
        testConfig[TEST_CONFIG_OTHER_FILES] = String.Join(" ", otherFiles);
        otherFilesCount++;
      }
      return testConfig;
    }

    private static KeyValuePair<string, string> ParseDafnyArgument(string argument) {
      if (argument.StartsWith("-") || argument.StartsWith("/")) {
        argument = argument.Substring(1);
        int colonIndex = argument.IndexOf(":");
        if (colonIndex >= 0) {
          return new KeyValuePair<string, string>(
              argument.Substring(0, colonIndex),
              argument.Substring(colonIndex + 1));
        } else {
          return new KeyValuePair<string, string>(argument, "yes");
        }
      } else {
        return new KeyValuePair<string, string>(TEST_CONFIG_OTHER_FILES, argument);
      }
    }

    public void Run(string root) {
      // TODO-RS: Search for "*.transcript" too
      foreach (var file in Directory.GetFiles(root, "*.dfy", SearchOption.AllDirectories)) {
        try {
          count++;
          ConvertLitTest(file);
        } catch (ArgumentException e) {
          invalidCount++;
          Console.WriteLine(file + ": " + e.Message);
        }
      }
      Console.WriteLine("Default: " + defaultCount + "/" + count);
      Console.WriteLine("Verify only: " + verifyOnlyCount + "/" + count);
      Console.WriteLine("With other files: " + otherFilesCount + "/" + count);
      Console.WriteLine("Invalid: " + invalidCount + "/" + count);
    }
    
    public static void Main(string[] args) { 
      new LitTestConvertor().Run(args[0]);
    }
  }
}