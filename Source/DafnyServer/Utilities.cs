// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

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

    internal static void ApplyArgs(string[] args, DafnyOptions options) {
      Dafny.DafnyOptions.Install(options);
      Dafny.DafnyOptions.O.TimeLimit = 10; //This is just a default; it can be overriden
      DafnyOptions.O.VerifySnapshots = 3;

      if (DafnyOptions.O.Parse(args)) {
        DafnyOptions.O.VcsCores = Math.Max(1, System.Environment.ProcessorCount / 2); // Don't use too many cores
        DafnyOptions.O.PrintTooltips = true; // Dump tooltips (ErrorLevel.Info) to stdout
        //DafnyOptions.O.UnicodeOutput = true; // Use pretty warning signs
        DafnyOptions.O.ShowSnippets = false; // Server sometimes has filename == null, which crashes showSnippets
        DafnyOptions.O.TraceProofObligations = true; // Show which method is being verified, but don't show duration of verification
      } else {
        throw new ServerException("Invalid command line options");
      }
    }
  }
}
