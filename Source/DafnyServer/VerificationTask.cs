using System;
using System.IO;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Json;
using System.Text;

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
        Interaction.EOM(Interaction.SUCCESS, (string)null);
      } catch (Exception ex) {
        Interaction.EOM(Interaction.FAILURE, ex);
      }
    }

    internal void Run() {
      new DafnyHelper(args, filename, ProgramSource).Verify();
    }

    internal void Symbols() {
      new DafnyHelper(args, filename, ProgramSource).Symbols();
    }

    public void CounterExample() {
      new DafnyHelper(args, filename, ProgramSource).CounterExample();
    }

    public void DotGraph() {
      new DafnyHelper(args, filename, ProgramSource).DotGraph();
    }

    public void Unmarshal() {
      Console.WriteLine(ProgramSource);
    }
  }
}
