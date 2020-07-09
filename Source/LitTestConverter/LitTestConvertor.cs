using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using Microsoft.SqlServer.Server;

namespace DafnyTests {
    public static class LitTestConvertor {
        
        private const string LIT_COMMAND_PREFIX = "// RUN: ";
        private const string LIT_DAFNY = "%dafny";
        private const string DAFNY_COMPILE = "/compile:";
        private const string DAFNY_COMPILE_TARGET = "/compileTarget:";

        private static readonly string[] IGNORED_DAFNY_COMMAND_ARGUMENTS = {
            "/print:\"%t.print\"", 
            "/dprint:\"%t.dprint\"",
            "/dprint:\"%t.dfy\"",
            "/rprint:\"%t.rprint\"", 
            "/rprint:\"%t.dprint\"",
            "/dprint:\"%t.dprint.dfy\"",
            
            "\"%s\"", ">", ">>", "\"%t\""
        };

        private static readonly string[] SUPPORTED_DAFNY_FLAGS = {
            "/autoTriggers",
            "/verifyAllModules",
            "/allocated",
            "/printTooltips",
            "/env",
            "/ironDafny",
            "/definiteAssignment",
            "/tracePOs",
            "/optimizeResolution",
            "/warnShadowing",
            "/verifySnapshots",
            "/traceCaching",
            "/noNLarith",
            "/errorTrace",
            "/arith",
            "/noVerify",
            "/dafnyVerify",
            "/optimize",
            // TODO-RS: Catch %t here?
            "/dprint",
            "/rprint"
        };
        
        public static void ConvertLitTest(string filePath) {
            string[] lines = File.ReadAllLines(filePath);
            if (lines.Length < 2) {
                throw new ArgumentException("Not enough lines to match expected lit test pattern");
            }
            
            string dafnyCommand = ExtractLitCommand(lines[0]);
            if (dafnyCommand == null) {
                // Doesn't look like a lit test
                return;
            }
            if (!dafnyCommand.StartsWith(LIT_DAFNY)) {
                throw new ArgumentException("First lit command is not expected %dafny: " + dafnyCommand);
            }
            var testConfig = ParseDafnyCommand(dafnyCommand.Substring(LIT_DAFNY.Length));
            
            string diffCommand = ExtractLitCommand(lines[1]);
            if (!diffCommand.Equals("%diff \"%s.expect\" \"%t\"")) {
                throw new ArgumentException("Second lit command is not expected %diff: " + diffCommand);
            }
        }

        private static string ExtractLitCommand(string line) {
            if (!line.StartsWith(LIT_COMMAND_PREFIX)) {
                return null;
            }
            return line.Substring(LIT_COMMAND_PREFIX.Length);
        }
        
        private static Dictionary<string, string> ParseDafnyCommand(string line) {
            var testConfig = new Dictionary<string, string>();
            var parts = line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
            int compileLevel;
            // Check the arguments for anything non-standard
            foreach (var argument in parts) {
                if (IGNORED_DAFNY_COMMAND_ARGUMENTS.Contains(argument)) {
                    // Ignore
                } else if (argument.StartsWith(DAFNY_COMPILE)) {
                    compileLevel = Int32.Parse(argument.Substring(DAFNY_COMPILE.Length));
                } else if (argument.StartsWith(DAFNY_COMPILE_TARGET)) {
                    // Ignore - assume it will work for all target language unless proven otherwise
                } else {
                    KeyValuePair<string, string> pair = ParseDafnyArgument(argument);
                    testConfig.Add(pair.Key, pair.Value);
                }
            }

            return testConfig;
        }

        private static KeyValuePair<string, string> ParseDafnyArgument(string argument) {
            foreach (var supportedFlag in SUPPORTED_DAFNY_FLAGS) {
                if (argument.StartsWith(supportedFlag)) {
                    if (argument.Equals(supportedFlag)) {
                        return new KeyValuePair<string, string>(supportedFlag, "yes");
                    } else if (argument[supportedFlag.Length] == ':') {
                        return new KeyValuePair<string, string>(supportedFlag,
                            argument.Substring(supportedFlag.Length + 1));
                    }
                }
            }
            throw new ArgumentException("Unrecognized dafny argument: " + argument);
        }

        public static void Main(string[] args) {
            var root = args[0];
            var count = 0;
            var invalidCount = 0;
            foreach (var file in Directory.GetFiles(root, "*.dfy", SearchOption.AllDirectories)) {
                try {
                    count++;
                    ConvertLitTest(file);
                } catch (ArgumentException e) {
                    invalidCount++;
                    Console.WriteLine(file + ": " + e.Message);
                }
            }
            Console.WriteLine(invalidCount + "/" + count);
        }
    }
}