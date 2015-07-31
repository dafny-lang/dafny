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
  class Interaction {
    internal static string SUCCESS = "SUCCESS";
    internal static string FAILURE = "FAILURE";
    internal static string SERVER_EOM_TAG = "[[DAFNY-SERVER: EOM]]";
    internal static string CLIENT_EOM_TAG = "[[DAFNY-CLIENT: EOM]]";

    internal static void EOM(string header, string msg) {
      var trailer = (msg == null) ? "" : "\n";
      Console.Write("{0}{1}[{2}] {3}\n", msg ?? "", trailer, header, SERVER_EOM_TAG);
      Console.Out.Flush();
    }

    internal static void EOM(string header, Exception ex, string subHeader="") {
      var aggregate = ex as AggregateException;
      subHeader = String.IsNullOrEmpty(subHeader) ? "" : subHeader + " ";

      if (aggregate == null) {
        EOM(header, subHeader + ex.Message);
      } else {
        EOM(header, subHeader + aggregate.InnerExceptions.MapConcat(exn => exn.Message, ", "));
      }
    }
  }

  // FIXME: This should not be duplicated here
  class DafnyConsolePrinter : ConsolePrinter {
    public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null) {
      // Dafny has 0-indexed columns, but Boogie counts from 1
      var realigned_tok = new Token(tok.line, tok.col - 1);
      realigned_tok.kind = tok.kind;
      realigned_tok.pos = tok.pos;
      realigned_tok.val = tok.val;
      realigned_tok.filename = tok.filename;
      base.ReportBplError(realigned_tok, message, error, tw, category);

      if (tok is Dafny.NestedToken) {
        var nt = (Dafny.NestedToken)tok;
        ReportBplError(nt.Inner, "Related location", false, tw);
      }
    }
  }

  [Serializable]
  class VerificationTask {
    [DataMember]
    string[] args = null;

    [DataMember]
    string filename = null;

    [DataMember]
    string source = null;

    [DataMember]
    bool sourceIsFile = false;

    string ProgramSource { get { return sourceIsFile ? File.ReadAllText(source) : source; } }

    internal static VerificationTask ReadTask(string b64_repr) {
      try {
        var json = Encoding.UTF8.GetString(System.Convert.FromBase64String(b64_repr));
        using (MemoryStream ms = new MemoryStream(Encoding.Unicode.GetBytes(json))) {
          DataContractJsonSerializer serializer = new DataContractJsonSerializer(typeof(VerificationTask));
          return (VerificationTask)serializer.ReadObject(ms);
        }
      } catch (Exception ex) {
        throw new ServerException("Deserialization failed: {0}.", ex.Message);
      }
    }

    internal static void SelfTest() {
      var task = new VerificationTask() { 
        filename = "<none>", 
        sourceIsFile = false, 
        args = new string[] { },
        source = "method selftest() { assert true; }"
      };
      try {
        task.Run();
        Interaction.EOM(Interaction.SUCCESS, null);
      } catch (Exception ex) {
        Interaction.EOM(Interaction.FAILURE, ex);
      }
    }

    internal void Run() {
      Server.ApplyArgs(args);
      new DafnyHelper(filename, ProgramSource).Verify();
    }
  }

  class ServerException : Exception {
    internal ServerException(string message) : base(message) { }
    internal ServerException(string message, params object[] args) : base(String.Format(message, args)) { }
  }

  class Server {
    private bool running;

    static void Main(string[] args) {
      Server server = new Server();
      if (args.Length > 0) {
        if (args[0] == "selftest") {
          VerificationTask.SelfTest();
        } else if (File.Exists(args[0])) {
          Console.SetIn(new StreamReader(args[0]));
          server.Loop();
        } else {
          Console.WriteLine("Not sure what to do with '{0}'", String.Join(" ", args));
        }
      } else {
        server.Loop();
      }
    }

    public Server() {
      this.running = true;
      Console.CancelKeyPress += this.CancelKeyPress;
      ExecutionEngine.printer = new DafnyConsolePrinter();
    }

    internal static void ApplyArgs(string[] args) {
      Dafny.DafnyOptions.Install(new Dafny.DafnyOptions());
      if (CommandLineOptions.Clo.Parse(args)) {
        // Dafny.DafnyOptions.O.ErrorTrace = 0; //FIXME
        // Dafny.DafnyOptions.O.ModelViewFile = "-";
        Dafny.DafnyOptions.O.ProverKillTime = 10;
        Dafny.DafnyOptions.O.VcsCores = Math.Max(1, System.Environment.ProcessorCount - 1);
        Dafny.DafnyOptions.O.VerifySnapshots = 2;
      } else {
        throw new ServerException("Invalid command line options");
      }
    }

    void CancelKeyPress(object sender, ConsoleCancelEventArgs e) {
      e.Cancel = true;
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
        var command = line.Split();
        Respond(command);
      }
    }

    void Respond(string[] command) {
      try {
        if (command.Length ==  0) {
          throw new ServerException("Empty command");
        }

        var verb = command[0];
        if (verb == "verify") {
          checkArgs(command, 0);
          var payload = ReadPayload();
          VerificationTask.ReadTask(payload).Run();
        } else if (verb == "quit") {
          checkArgs(command, 0);
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

    void checkArgs(string[] command, int expectedLength) {
      if (command.Length - 1 != expectedLength) {
        throw new ServerException("Invalid argument count (got {0}, expected {1})", command.Length - 1, expectedLength);
      }
    }

    void Exit() {
      this.running = false;
    }
  }

  class DafnyHelper {
    private string fname;
    private string source;

    private Dafny.Errors errors;
    private Dafny.Program dafnyProgram;
    private Bpl.Program boogieProgram;

    public DafnyHelper(string fname, string source) {
      this.fname = fname;
      this.source = source;
      this.errors = new Dafny.Errors();
    }

    public bool Verify() {
      return Parse() && Resolve() && Translate() && Boogie();
    }

    private bool Parse() {
      Dafny.ModuleDecl module = new Dafny.LiteralModuleDecl(new Dafny.DefaultModuleDecl(), null);
      Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
      var success = (Dafny.Parser.Parse(source, fname, fname, module, builtIns, errors) == 0 &&
                     Dafny.Main.ParseIncludes(module, builtIns, new List<string>(), errors) == null);
      if (success) {
        dafnyProgram = new Dafny.Program(fname, module, builtIns);
      }
      return success;
    }

    private bool Resolve() {
      var resolver = new Dafny.Resolver(dafnyProgram);
      resolver.ResolveProgram(dafnyProgram);
      return resolver.ErrorCount == 0;
    }

    private bool Translate() {
      var translator = new Dafny.Translator() { InsertChecksums = true, UniqueIdPrefix = null }; //FIXME check if null is OK for UniqueIdPrefix
      boogieProgram = translator.Translate(dafnyProgram); // FIXME how are translation errors reported?
      return true;
    }

    private bool Boogie() {
      if (boogieProgram.Resolve() == 0 && boogieProgram.Typecheck() == 0) { //FIXME ResolveAndTypecheck?
        ExecutionEngine.EliminateDeadVariables(boogieProgram);
        ExecutionEngine.CollectModSets(boogieProgram);
        ExecutionEngine.CoalesceBlocks(boogieProgram);
        ExecutionEngine.Inline(boogieProgram);

        switch (ExecutionEngine.InferAndVerify(boogieProgram, new PipelineStatistics(), "ServerProgram", null, DateTime.UtcNow.Ticks.ToString())) { // FIXME check if null is ok for error delegate
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            return true;
        }
      }

      return false;
    }
  }
}