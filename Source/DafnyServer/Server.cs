// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.IO;
using System.Text;
using System.Threading.Tasks;
using DafnyServer;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Server : IDisposable {
    private bool running;
    private readonly ExecutionEngine engine;
    private readonly TextReader input;
    private readonly TextWriter outputWriter;

    public static Task<int> Main(string[] args) {
      return MainWithWriters(Console.Out, Console.Error, Console.In, args);
    }

    public static async Task<int> MainWithWriters(TextWriter outputWriter, TextWriter errorWriter, TextReader inputReader, string[] args) {
      var options = DafnyOptions.CreateUsingOldParser(outputWriter);
      options.Printer = new DafnyConsolePrinter(options);
      options.Set(CommonOptionBag.AllowAxioms, true);
      Console.SetError(outputWriter);
      ServerUtils.ApplyArgs(args, options);
      options.ProcessSolverOptions(new ErrorReporterSink(options), Token.NoToken);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);

      // read the optional flag (only one flag is allowed)
      bool plaintext = false;
      bool selftest = false;
      bool decode = false;
      bool encode = false;
      var n = 0;  // number of consumed args
      var arg = n < args.Length ? args[n] : null;
      if (arg == "-plaintext") {
        plaintext = true;
        n++;
      } else if (arg == "-selftest") {
        selftest = true;
        n++;
      } else if (arg == "-decode") {
        decode = true;
        n++;
      } else if (arg == "-encode") {
        encode = true;
        n++;
      }

      if (selftest) {
        await VerificationTask.SelfTest(options, engine);
        return 0;
      }

      if (n < args.Length) {
        var inputFilename = args[n];
        if (File.Exists(inputFilename)) {
          await outputWriter.WriteLineAsync($"# Reading from {Path.GetFileName(inputFilename)}");
          inputReader = new StreamReader(inputFilename, Encoding.UTF8);
        } else {
          await outputWriter.WriteLineAsync($"Error: file '{inputFilename}' does not exist");
        }
      }
      var server = new Server(engine, inputReader, outputWriter);

      if (decode) {
        server.Decode();
      } else if (encode) {
        server.Encode();
      } else {
        await server.Loop(options, plaintext);
      }
      return 0;
    }

    private void SetupConsole() {
      // Setting InputEncoding to UTF8 causes z3 to choke.
      Console.OutputEncoding = new UTF8Encoding(false, true);
    }

    public Server(ExecutionEngine engine, TextReader input, TextWriter outputWriter) {
      this.engine = engine;
      this.input = input;
      this.outputWriter = outputWriter;
      this.running = true;
      SetupConsole();
    }

    bool EndOfPayload(out string line) {
      line = input.ReadLine();
      return line == null || line == Interaction.CLIENT_EOM_TAG;
    }

    string ReadPayload(bool inputIsPlaintext) {
      StringBuilder buffer = new StringBuilder();
      while (!EndOfPayload(out var line)) {
        buffer.Append(line);
        if (inputIsPlaintext) {
          buffer.Append("\n");
        }
      }
      return buffer.ToString();
    }

    /// <summary>
    /// Copy input, but decode each (presumed encoded) payload.
    /// Leave payload of marshal and unmarshal unchanged.
    /// </summary>
    void Decode() {
      while (true) {
        var line = input.ReadLine();
        if (line == null) {
          return;
        }
        outputWriter.WriteLine(line);
        if (line != String.Empty && !line.StartsWith("#")) {
          // assume the line to be a command
          var vt = ReadVerificationTask(line == "marshal");
          outputWriter.WriteLine(vt.ProgramSource);
          outputWriter.WriteLine(Interaction.CLIENT_EOM_TAG);
        }
      }
    }

    /// <summary>
    /// Copy input, but encode each (presumed plaintext) payload.
    /// Leave payload of marshal and unmarshal unchanged.
    /// </summary>
    void Encode() {
      while (true) {
        var line = input.ReadLine();
        if (line == null) {
          return;
        }
        outputWriter.WriteLine(line);
        if (line != String.Empty && !line.StartsWith("#")) {
          // assume the line to be a command
          var vt = ReadVerificationTask(line != "unmarshal");
          if (line != "unmarshal") {
            var b64Repr = vt.EncodeProgram(out _);
            WriteAcrossLines(b64Repr, 76);
          } else {
            // for unmarshal, pass the line through unchanged
            outputWriter.WriteLine(vt.ProgramSource);
          }
          outputWriter.WriteLine(Interaction.CLIENT_EOM_TAG);
        }
      }
    }

    /// <summary>
    /// Writes "s" across lines, so that all lines have "width" characters,
    /// except that the last line, if any, may have (more than 0 and) up to
    /// "width" characters.
    /// </summary>
    /// <param name="s">assumed not to contain any newline characters</param>
    /// <param name="width">assumed to be positive</param>
    void WriteAcrossLines(string s, int width) {
      var len = s.Length;
      for (var n = 0; n < len; n += width) {
        var next = n + width <= len ? s.Substring(n, width) : s.Substring(n);
        outputWriter.WriteLine(next);
      }
    }

    async Task Loop(DafnyOptions options, bool inputIsPlaintext) {
      for (int cycle = 0; running; cycle++) {
        var line = await input.ReadLineAsync() ?? "quit";
        if (line != String.Empty && !line.StartsWith("#")) {
          var command = line.Split();
          await Respond(options, command, inputIsPlaintext);
        }
      }
    }

    async Task Respond(DafnyOptions options, string[] command, bool inputIsPlaintext) {
      try {
        if (command.Length == 0) {
          throw new ServerException("Empty command");
        }

        var verb = command[0];
        var msg = "Verification completed successfully!";
        if (verb == "verify") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          await vt.Run(options, engine);
        } else if (verb == "counterexample") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          await vt.CounterExample(options, engine);
        } else if (verb == "dotgraph") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          await vt.DotGraph(options, engine);
        } else if (verb == "symbols") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          await vt.Symbols(options, engine);
        } else if (verb == "version") {
          ServerUtils.checkArgs(command, 0);
          var _ = ReadVerificationTask(inputIsPlaintext);
          VersionCheck.CurrentVersion();
        } else if (verb == "unmarshal") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(false);
          vt.Unmarshal(outputWriter, command);
          msg = null;
        } else if (verb == "marshal") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(true);
          vt.Marshal(outputWriter, command);
          msg = null;
        } else if (verb == "quit") {
          ServerUtils.checkArgs(command, 0);
          Exit();
          return;  // don't print EOM message
        } else {
          throw new ServerException("Unknown verb '{0}'", verb);
        }

        Interaction.Eom(outputWriter, Interaction.SUCCESS, msg);
      } catch (ServerException ex) {
        Interaction.Eom(outputWriter, Interaction.FAILURE, ex);
      } catch (Exception ex) {
        Interaction.Eom(outputWriter, Interaction.FAILURE, ex, "[FATAL]");
        running = false;
      }
    }

    VerificationTask ReadVerificationTask(bool inputIsPlaintext) {
      var payload = ReadPayload(inputIsPlaintext);
      if (inputIsPlaintext) {
        return new VerificationTask([], "transcript", payload, false);
      } else {
        return VerificationTask.ReadTask(payload);
      }
    }

    void Exit() {
      this.running = false;
      Dispose();
    }

    public void Dispose() {
      engine.Dispose();
    }
  }

}
