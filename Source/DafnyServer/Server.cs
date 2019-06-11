using System;
using System.IO;
using System.Text;
using DafnyServer;
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
        Console.SetIn(new StreamReader(arg, Encoding.UTF8));
        server.Loop();
      } else {
        server.Loop();
      }
    }

    private void SetupConsole() {
      // Setting InputEncoding to UTF8 causes z3 to choke.
      Console.OutputEncoding = new UTF8Encoding(false, true);
    }

    public Server() {
      this.running = true;
      ExecutionEngine.printer = new DafnyConsolePrinter();
      SetupConsole();
    }

    bool EndOfPayload(out string line) {
      line = Console.ReadLine();
      return line == null || line == Interaction.CLIENT_EOM_TAG;
    }

    string ReadPayload() {
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
        if (command.Length == 0) {
          throw new ServerException("Empty command");
        }

        var verb = command[0];
        if (verb == "verify") {
          ServerUtils.checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).Run();
        } else if (verb == "counterExample") {
          ServerUtils.checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).CounterExample();
        } else if (verb == "dotgraph") {
          ServerUtils.checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).DotGraph();
        } else if (verb == "symbols") {
          ServerUtils.checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).Symbols();
        } else if (verb == "version") {
          ServerUtils.checkArgs(command, 0);
          ReadPayload();
          VersionCheck.CurrentVersion();
        } else if (verb == "unmarshal") {
          ServerUtils.checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).Unmarshal();
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
