// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.IO;
using System.Text;
using DafnyServer;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Server {
    private bool running;
    private readonly ExecutionEngine engine;

    static void Main(string[] args) {
      var options = DafnyOptions.Create();
      ServerUtils.ApplyArgs(args, options);
      var engine = ExecutionEngine.CreateWithoutSharedCache(options);
      Server server = new Server(engine);

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
        VerificationTask.SelfTest(options, engine);
        return;
      }

      if (n < args.Length) {
        var inputFilename = args[n];
        if (File.Exists(inputFilename)) {
          Console.WriteLine("# Reading from {0}", Path.GetFileName(inputFilename));
          Console.SetIn(new StreamReader(inputFilename, Encoding.UTF8));
        } else {
          Console.WriteLine("Error: file '{0}' does not exist", inputFilename);
        }
      }

      if (decode) {
        server.Decode();
      } else if (encode) {
        server.Encode();
      } else {
        server.Loop(options, plaintext);
      }
    }

    private void SetupConsole() {
      // Setting InputEncoding to UTF8 causes z3 to choke.
      Console.OutputEncoding = new UTF8Encoding(false, true);
    }

    public Server(ExecutionEngine engine) {
      this.engine = engine;
      this.running = true;
      SetupConsole();
    }

    bool EndOfPayload(out string line) {
      line = Console.ReadLine();
      return line == null || line == Interaction.CLIENT_EOM_TAG;
    }

    string ReadPayload(bool inputIsPlaintext) {
      StringBuilder buffer = new StringBuilder();
      string line = null;
      while (!EndOfPayload(out line)) {
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
        var line = Console.ReadLine();
        if (line == null) {
          return;
        }
        Console.WriteLine(line);
        if (line != String.Empty && !line.StartsWith("#")) {
          // assume the line to be a command
          var vt = ReadVerificationTask(line == "marshal");
          Console.WriteLine(vt.ProgramSource);
          Console.WriteLine(Interaction.CLIENT_EOM_TAG);
        }
      }
    }

    /// <summary>
    /// Copy input, but encode each (presumed plaintext) payload.
    /// Leave payload of marshal and unmarshal unchanged.
    /// </summary>
    void Encode() {
      while (true) {
        var line = Console.ReadLine();
        if (line == null) {
          return;
        }
        Console.WriteLine(line);
        if (line != String.Empty && !line.StartsWith("#")) {
          // assume the line to be a command
          var vt = ReadVerificationTask(line != "unmarshal");
          if (line != "unmarshal") {
            var b64Repr = vt.EncodeProgram(out _);
            WriteAcrossLines(b64Repr, 76);
          } else {
            // for unmarshal, pass the line through unchanged
            Console.WriteLine(vt.ProgramSource);
          }
          Console.WriteLine(Interaction.CLIENT_EOM_TAG);
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
    static void WriteAcrossLines(string s, int width) {
      var len = s.Length;
      for (var n = 0; n < len; n += width) {
        var next = n + width <= len ? s.Substring(n, width) : s.Substring(n);
        Console.WriteLine(next);
      }
    }

    void Loop(DafnyOptions options, bool inputIsPlaintext) {
      for (int cycle = 0; running; cycle++) {
        var line = Console.ReadLine() ?? "quit";
        if (line != String.Empty && !line.StartsWith("#")) {
          var command = line.Split();
          Respond(options, command, inputIsPlaintext);
        }
      }
    }

    void Respond(DafnyOptions options, string[] command, bool inputIsPlaintext) {
      try {
        if (command.Length == 0) {
          throw new ServerException("Empty command");
        }

        var verb = command[0];
        var msg = "Verification completed successfully!";
        if (verb == "verify") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          vt.Run(options, engine);
        } else if (verb == "counterexample") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          vt.CounterExample(options, engine);
        } else if (verb == "dotgraph") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          vt.DotGraph(options, engine);
        } else if (verb == "symbols") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(inputIsPlaintext);
          vt.Symbols(options, engine);
        } else if (verb == "version") {
          ServerUtils.checkArgs(command, 0);
          var _ = ReadVerificationTask(inputIsPlaintext);
          VersionCheck.CurrentVersion();
        } else if (verb == "unmarshal") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(false);
          vt.Unmarshal(command);
          msg = null;
        } else if (verb == "marshal") {
          ServerUtils.checkArgs(command, 0);
          var vt = ReadVerificationTask(true);
          vt.Marshal(command);
          msg = null;
        } else if (verb == "quit") {
          ServerUtils.checkArgs(command, 0);
          Exit();
          return;  // don't print EOM message
        } else {
          throw new ServerException("Unknown verb '{0}'", verb);
        }

        Interaction.EOM(Interaction.SUCCESS, msg);
      } catch (ServerException ex) {
        Interaction.EOM(Interaction.FAILURE, ex);
      } catch (Exception ex) {
        Interaction.EOM(Interaction.FAILURE, ex, "[FATAL]");
        running = false;
      }
    }

    VerificationTask ReadVerificationTask(bool inputIsPlaintext) {
      var payload = ReadPayload(inputIsPlaintext);
      if (inputIsPlaintext) {
        return new VerificationTask(Array.Empty<string>(), "transcript", payload, false);
      } else {
        return VerificationTask.ReadTask(payload);
      }
    }

    void Exit() {
      this.running = false;
    }
  }

}