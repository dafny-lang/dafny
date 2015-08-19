using System;
using System.IO;
using System.Text;
using System.Collections.Generic;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;
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

    internal static void EOM(string header, Exception ex, string subHeader = "") {
      var aggregate = ex as AggregateException;
      subHeader = String.IsNullOrEmpty(subHeader) ? "" : subHeader + " ";

      if (aggregate == null) {
        EOM(header, subHeader + ex.Message);
      } else {
        EOM(header, subHeader + aggregate.InnerExceptions.MapConcat(exn => exn.Message, ", "));
      }
    }
  }

  class ServerException : Exception {
    internal ServerException(string message) : base(message) { }
    internal ServerException(string message, params object[] args) : base(String.Format(message, args)) { }
  }

  class ServerUtils {
    internal static void checkArgs(string[] command, int expectedLength) {
      if (command.Length - 1 != expectedLength) {
        throw new ServerException("Invalid argument count (got {0}, expected {1})", command.Length - 1, expectedLength);
      }
    }

    internal static void ApplyArgs(string[] args, bool trace) {
      Dafny.DafnyOptions.Install(new Dafny.DafnyOptions());
      Dafny.DafnyOptions.O.ProverKillTime = 10;

      if (CommandLineOptions.Clo.Parse(args)) {
        // Dafny.DafnyOptions.O.ErrorTrace = 0; //FIXME
        // Dafny.DafnyOptions.O.ModelViewFile = "-";
        Dafny.DafnyOptions.O.UnicodeOutput = true;
        Dafny.DafnyOptions.O.VerifySnapshots = 2;
        Dafny.DafnyOptions.O.VcsCores = Math.Max(1, System.Environment.ProcessorCount - 1);
        Dafny.DafnyOptions.O.Trace = trace;
      } else {
        throw new ServerException("Invalid command line options");
      }
    }
  }
}
