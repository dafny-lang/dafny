using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

namespace DafnyTests {
    public static class LitTestConvertor {
        
        private const string LIT_COMMAND_PREFIX = "// RUN: ";
        private const string LIT_DIFF = "%diff";
        private const string LIT_DAFNY = "%dafny";
        private const string DAFNY_COMPILE = "/compile:";
        private const string DAFNY_COMPILE_TARGET = "/compileTarget:";
        private const string DAFNY_AUTO_TRIGGERS = "/autoTriggers:";
        private const string DAFNY_VERIFY_ALL_MODULES = "/verifyAllModules";
        private const string DAFNY_ALLOCATED = "/allocated:";

        private static readonly string[] IGNORED_DAFNY_COMMAND_ARGUMENTS = {
            "/print:\"%t.print\"", 
            "/dprint:\"%t.dprint\"", 
            "/rprint:\"%t.rprint\"", 
            "/rprint:\"%t.dprint\"",
            "\"%s\"", ">", ">>", "\"%t\""
        };
        
        public static void ConvertLitTest(string filePath) {
            var compileLevel = 1;
            var printToolTips = false;
            var autoTriggers = 1;
            var verifyAllModules = false;
            var allocated = 3;
            var reader = new StreamReader(filePath);
            
            string line;  
            while((line = reader.ReadLine()) != null) {
                if (line.StartsWith(LIT_COMMAND_PREFIX)) {
                    var parts = line.Substring(LIT_COMMAND_PREFIX.Length)
                                    .Split((char[])null, StringSplitOptions.RemoveEmptyEntries);
                    switch (parts[0]) {
                        case LIT_DIFF:
                            // Ignore: assume that if this is anything other than the standard
                            // %diff "%s.expect" "%t" line, then at least one other line will be non-standard
                            // as well (to produce the non-standard arguments)
                            break;
                        case LIT_DAFNY:
                            // Check the arguments for anything non-standard
                            foreach (var arg in parts.Skip(1)) {
                                if (IGNORED_DAFNY_COMMAND_ARGUMENTS.Contains(arg)) {
                                    // Ignore
                                } else if (arg.Equals("/printTooltips")) {
                                    printToolTips = true;
                                } else if (arg.Equals(DAFNY_VERIFY_ALL_MODULES)) {
                                    verifyAllModules = true;
                                } else if (arg.StartsWith(DAFNY_COMPILE)) {
                                    compileLevel = Int32.Parse(arg.Substring(DAFNY_COMPILE.Length));
                                } else if (arg.StartsWith(DAFNY_ALLOCATED)) {
                                    allocated = Int32.Parse(arg.Substring(DAFNY_ALLOCATED.Length));
                                } else if (arg.StartsWith(DAFNY_COMPILE_TARGET)) {
                                    // Ignore - assume it will work for all target language unless proven otherwise
                                } else {
                                    throw new ArgumentException("Unrecognized dafny argument: " + arg);
                                }
                            }
                            break;
                        default:
                            throw new ArgumentException("Unrecognized lit command format: " + line);
                    }
                }
            }  
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