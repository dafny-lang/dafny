using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class ShellLitCommand : ILitCommand {
    private string shellCommand;
    private string[] arguments;
    private string[] passthroughEnvironmentVariables;

    public ShellLitCommand(string shellCommand, IEnumerable<string> arguments, IEnumerable<string> passthroughEnvironmentVariables) {
      this.shellCommand = shellCommand;
      this.arguments = arguments.ToArray();
      this.passthroughEnvironmentVariables = passthroughEnvironmentVariables.ToArray();
    }

    public (int, string, string) Execute(ITestOutputHelper? outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      using var process = new Process();

      process.StartInfo.FileName = shellCommand;
      foreach (var argument in arguments) {
        process.StartInfo.ArgumentList.Add(argument);
      }

      // We avoid setting the current directory so that we maintain parity with
      // MainMethodLitCommand, which can't change the current directory.

      process.StartInfo.UseShellExecute = false;
      process.StartInfo.RedirectStandardInput = true;
      process.StartInfo.RedirectStandardOutput = true;
      process.StartInfo.RedirectStandardError = true;

      process.StartInfo.EnvironmentVariables.Clear();
      foreach (var passthrough in passthroughEnvironmentVariables) {
        process.StartInfo.EnvironmentVariables.Add(passthrough, Environment.GetEnvironmentVariable(passthrough));
      }

      // Getting console encodings right is tricky on Windows.
      //
      // Some background: the current console has a codepage, which is what
      // programs that output text are supposed to use.  The command `chcp` can
      // be used to test or set it:
      //
      // > chcp
      // Active code page: 1252
      //
      // So, if the console has its codepage set to 850 (the old IBM codepage),
      // then a program that wants to print `é` (U+00E9, Latin Small Letter E
      // With Acute) should output a single byte, #x82.  But if the codepage is
      // 1252 (Latin 1), then that same program should output the single
      // byte `#xE9`.  Finally, if the codepage is 65001 (UTF8), then that same
      // program should output `#xC3 #xA9`.
      //
      // Thankfully, the C# runtime takes care of this for us.  It uses
      // `GetConsoleCP` to determine what encoding to use, then uses that when
      // `Console.WriteLine` is called (and replaces unsupported characters by
      // the fallback character `?`).  Here is a concrete demo, with character
      // U+20AC (€) (which is supported by codepage 65001 but not 850):
      //
      // > mkdir demo
      // > cd demo
      // > dotnet new console
      // > ECHO Console.WriteLine(new char[] { (char)0x20AC }); > Program.cs
      // > chcp 65001 && dotnet run
      // Active code page: 65001
      // €
      // > chcp 850 && dotnet run
      // Active code page: 850
      // ?
      //
      // So, the proper way to run a program that might print non-ASCII
      // characters is to set the console's code page to 65001.  This is done by
      // the user before calling dotnet run, so nothing to do here.
      //
      // … but this is not enough, because some processes change the codepage
      // when they invoke a subprocess.  For example, Process.Start reuses the
      // current codepage, *unless* `CreateNoWindow` is true (in that case, the
      // codepage is reset to the default (this is explained nicely at
      // https://stackoverflow.com/questions/5094003/).
      //
      // So, one needs to set `CreateNoWindow` to false to avoid dreaded `?`
      // output, as is done below.
      //
      // … but this is not enough, because dotnet run (or XUnit) also resets the
      // codepage.  That's a bug there, and in the meantime the best hack we
      // have is to override that codepage by setting `OutputEncoding`.

      Console.OutputEncoding = Encoding.UTF8;
      process.StartInfo.CreateNoWindow = false;

      // Finally, for Java + Ubuntu, we make sure to set LANG:
      process.StartInfo.EnvironmentVariables["LANG"] = "C.UTF-8";
      // … and For Python + Windows, we set PYTHONIOENCODING
      process.StartInfo.EnvironmentVariables["PYTHONIOENCODING"] = "UTF-8";

      // Note that all of this, except the Console.OutputEncoding part, is necessary only if we run compiled Dafny
      // artifacts directly, since `dafny run` already enforces UTF-8 output.  The Console.OutputEncoding part is still
      // needed because that is also what C# will use to decode the output of `process`.

      process.Start();
      if (inputReader != null) {
        string input = inputReader.ReadToEnd();
        inputReader.Close();
        process.StandardInput.Write(input);
        process.StandardInput.Close();
      }

      // FIXME the code below will deadlock if process fills the stderr buffer.
      string output = process.StandardOutput.ReadToEnd();
      outputWriter?.Write(output);
      outputWriter?.Close();
      string error = process.StandardError.ReadToEnd();
      errorWriter?.Write(error);
      errorWriter?.Close();
      process.WaitForExit();

      return (process.ExitCode, output, error);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(shellCommand);
      builder.Append(' ');
      builder.AppendJoin(" ", arguments);
      return builder.ToString();
    }
  }
}
