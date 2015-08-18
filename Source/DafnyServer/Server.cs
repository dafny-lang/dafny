using System;
using System.IO;
using System.Text;
using System.Collections.Generic;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;

using Dafny = Microsoft.Dafny;
using Bpl = Microsoft.Boogie;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  class Server {
    private bool running;

    static void Main(string[] args) {
      Server server = new Server();

      var hasArg = args.Length > 0;
      var arg = hasArg ? args[0] : null;

      if (hasArg && args[0] == "selftest") {
        VerificationTask.SelfTest();
      } else if (hasArg && File.Exists(arg)) {
        Console.WriteLine("# Reading from {0}", Path.GetFileName(arg));
        Console.SetIn(new StreamReader(arg));
        server.Loop();
      } else {
        server.Loop();
      }
    }

    public Server() {
      this.running = true;
      Console.CancelKeyPress += this.CancelKeyPress;
      Console.InputEncoding = System.Text.Encoding.UTF8;
      Console.OutputEncoding = System.Text.Encoding.UTF8;
      ExecutionEngine.printer = new DafnyConsolePrinter();
    }

    void CancelKeyPress(object sender, ConsoleCancelEventArgs e) {
      // e.Cancel = true;
      // FIXME TerminateProver and RunningProverFromCommandLine
      // Cancel the current verification? TerminateProver() ? Or kill entirely?
    }

    static bool EndOfPayload(out string line) {
      line = Console.ReadLine();
      return line == null || line == Interaction.CLIENT_EOM_TAG;
    }

    static string ReadPayload() {
      StringBuilder buffer = new StringBuilder();
      string line = null;
      while (!EndOfPayload(out line)) {
        buffer.Append(line);
      }
      return buffer.ToString();
    }

    void Loop() {
      for (int cycle = 0; running; cycle++) {
        var line = Console.ReadLine() ?? "quit";
        if (line != String.Empty && !line.StartsWith("#")) {
          var command = line.Split();
          Respond(command);
        }
      }
    }

    void Respond(string[] command) {
      try {
        if (command.Length ==  0) {
          throw new ServerException("Empty command");
        }

        var verb = command[0];
        if (verb == "verify") {
          ServerUtils.checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).Run();
        } else if (verb == "quit") {
          ServerUtils.checkArgs(command, 0);
          Exit();
        } else {
          throw new ServerException("Unknown verb '{0}'", verb);
        }

        Interaction.EOM(Interaction.SUCCESS, "Verification completed successfully!");
      } catch (ServerException ex) {
        Interaction.EOM(Interaction.FAILURE, ex);
      } catch (Exception ex) {
        Interaction.EOM(Interaction.FAILURE, ex, "[FATAL]");
        running = false;
      }
    }

    void Exit() {
      this.running = false;
    }
  }

}