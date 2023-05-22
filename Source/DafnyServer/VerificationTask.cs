// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.IO;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;
using System.Text;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
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

    public VerificationTask(string[] args, string filename, string source, bool sourceIsFile) {
      this.args = args;
      this.filename = filename;
      this.source = source;
      this.sourceIsFile = sourceIsFile;
    }

    public string ProgramSource { get { return sourceIsFile ? File.ReadAllText(source) : source; } }

    internal static VerificationTask ReadTask(string b64Repr) {
      try {
        var json = Encoding.UTF8.GetString(System.Convert.FromBase64String(b64Repr));
        using (MemoryStream ms = new MemoryStream(Encoding.Unicode.GetBytes(json))) {
          DataContractJsonSerializer serializer = new DataContractJsonSerializer(typeof(VerificationTask));
          return (VerificationTask)serializer.ReadObject(ms);
        }
      } catch (Exception ex) {
        throw new ServerException("Deserialization failed: {0}.", ex.Message);
      }
    }

    internal static void SelfTest(DafnyOptions options, ExecutionEngine engine) {
      var task = new VerificationTask(new string[] { }, "<none>", "method selftest() { assert true; }", false);
      try {
        task.Run(options, engine);
        Interaction.EOM(Interaction.SUCCESS, (string)null);
      } catch (Exception ex) {
        Interaction.EOM(Interaction.FAILURE, ex);
      }
    }

    internal void Run(DafnyOptions options, ExecutionEngine engine) {
      new DafnyHelper(options, engine, args, filename, ProgramSource).Verify();
    }

    internal void Symbols(DafnyOptions options, ExecutionEngine engine) {
      new DafnyHelper(options, engine, args, filename, ProgramSource).Symbols();
    }

    public void CounterExample(DafnyOptions options, ExecutionEngine engine) {
      new DafnyHelper(options, engine, args, filename, ProgramSource).CounterExample();
    }

    public void DotGraph(DafnyOptions options, ExecutionEngine engine) {
      new DafnyHelper(options, engine, args, filename, ProgramSource).DotGraph();
    }

    public string EncodeProgram(out string json) {
      using (var ms = new MemoryStream()) {
        var serializer = new DataContractJsonSerializer(typeof(VerificationTask));
        serializer.WriteObject(ms, this);
        ms.Position = 0;
        var sr = new StreamReader(ms);
        json = sr.ReadToEnd();
      }
      return Convert.ToBase64String(Encoding.UTF8.GetBytes(json));
    }

    public void Marshal(string[] command) {
      try {
        var b64Repr = EncodeProgram(out var json);

        Console.WriteLine("# program source");
        Console.Write(ProgramSource);
        Console.WriteLine("# JSON encoding");
        Console.WriteLine(json);
        Console.WriteLine("# base64 encoding of JSON object");
        Console.WriteLine(b64Repr);
      } catch (Exception ex) {
        throw new ServerException("Serialization failed: {0}.", ex.Message);
      }
    }

    public void Unmarshal(string[] command) {
      Console.WriteLine($"# args: {Util.Comma(args)}");
      Console.WriteLine($"# filename: {filename}");
      Console.WriteLine($"# sourceIsFile: {sourceIsFile}");
      Console.WriteLine(ProgramSource);
    }
  }
}
