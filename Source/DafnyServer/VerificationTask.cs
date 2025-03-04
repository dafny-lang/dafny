// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.IO;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;
using System.Text;
using System.Threading.Tasks;
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

    internal static async Task SelfTest(DafnyOptions options, ExecutionEngine engine) {
      var task = new VerificationTask([], "<none>", "method selftest() { assert true; }", false);
      try {
        await task.Run(options, engine);
        Interaction.Eom(options.OutputWriter, Interaction.SUCCESS, (string)null);
      } catch (Exception ex) {
        Interaction.Eom(options.OutputWriter, Interaction.FAILURE, ex);
      }
    }

    internal Task<bool> Run(DafnyOptions options, ExecutionEngine engine) {
      return new DafnyHelper(options, engine, args, filename, ProgramSource).Verify();
    }

    internal Task Symbols(DafnyOptions options, ExecutionEngine engine) {
      return new DafnyHelper(options, engine, args, filename, ProgramSource).Symbols();
    }

    public Task CounterExample(DafnyOptions options, ExecutionEngine engine) {
      return new DafnyHelper(options, engine, args, filename, ProgramSource).CounterExample();
    }

    public Task DotGraph(DafnyOptions options, ExecutionEngine engine) {
      return new DafnyHelper(options, engine, args, filename, ProgramSource).DotGraph();
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

    public void Marshal(TextWriter outputWriter, string[] command) {
      try {
        var b64Repr = EncodeProgram(out var json);

        outputWriter.WriteLine("# program source");
        outputWriter.Write(ProgramSource);
        outputWriter.WriteLine("# JSON encoding");
        outputWriter.WriteLine(json);
        outputWriter.WriteLine("# base64 encoding of JSON object");
        outputWriter.WriteLine(b64Repr);
      } catch (Exception ex) {
        throw new ServerException("Serialization failed: {0}.", ex.Message);
      }
    }

    public void Unmarshal(TextWriter outputWriter, string[] command) {
      outputWriter.WriteLine($"# args: {Util.Comma(args)}");
      outputWriter.WriteLine($"# filename: {filename}");
      outputWriter.WriteLine($"# sourceIsFile: {sourceIsFile}");
      outputWriter.WriteLine(ProgramSource);
    }
  }
}
