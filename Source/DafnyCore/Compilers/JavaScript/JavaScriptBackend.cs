using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class JavaScriptBackend : ExecutableBackend {
  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".js" };

  public override string TargetLanguage => "JavaScript";
  public override string TargetExtension => "js";

  public override bool SupportsInMemoryCompilation => true;
  public override bool TextualTargetIsExecutable => true;

  public override IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string>(new List<string> { "number" });

  protected override SinglePassCompiler CreateCompiler() {
    return new JavaScriptCompiler(Options, Reporter);
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    compilationResult = null;
    if (runAfterCompile) {
      Contract.Assert(callToMain != null);  // this is part of the contract of CompileTargetProgram
                                            // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
                                            // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'node'
                                            // will run the program.
      return true;
    } else {
      // compile now
      return SendToNewNodeProcess(dafnyProgramName, targetProgramText, null, targetFilename, otherFileNames, outputWriter);
    }
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain /*?*/,
    string targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {

    return SendToNewNodeProcess(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames, outputWriter);
  }

  bool SendToNewNodeProcess(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
    TextWriter outputWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);

    var psi = new ProcessStartInfo("node", "") {
      RedirectStandardInput = true,
      RedirectStandardOutput = true,
      RedirectStandardError = true,
      StandardInputEncoding = Encoding.UTF8,
    };

    try {
      Process nodeProcess = Process.Start(psi);
      foreach (var filename in otherFileNames) {
        WriteFromFile(filename, nodeProcess.StandardInput);
      }
      nodeProcess.StandardInput.Write(targetProgramText);
      if (callToMain != null && Options.RunAfterCompile) {
        nodeProcess.StandardInput.WriteLine("require('process').stdout.setEncoding(\"utf-8\");");
        nodeProcess.StandardInput.WriteLine("require('process').argv = [\"node\",\"stdin\", " + string.Join(",", Options.MainArgs.Select(((JavaScriptCompiler)compiler).ToStringLiteral)) + "];");
        nodeProcess.StandardInput.Write(callToMain);
      }
      nodeProcess.StandardInput.Flush();
      nodeProcess.StandardInput.Close();
      // Fixes a problem of Node on Windows, where Node does not prints to the parent console its standard outputs.
      var errorProcessing = Task.Run(() => {
        // TODO fix.
        PassthroughBuffer(nodeProcess.StandardError, Options.ErrorWriter);
      });
      PassthroughBuffer(nodeProcess.StandardOutput, Options.OutputWriter);
      nodeProcess.WaitForExit();
#pragma warning disable VSTHRD002
      errorProcessing.Wait();
#pragma warning restore VSTHRD002
      return nodeProcess.ExitCode == 0;
    } catch (System.ComponentModel.Win32Exception e) {
      outputWriter.WriteLine("Error: Unable to start node.js ({0}): {1}", psi.FileName, e.Message);
      return false;
    }
  }

  public JavaScriptBackend(DafnyOptions options) : base(options) {
  }
}
