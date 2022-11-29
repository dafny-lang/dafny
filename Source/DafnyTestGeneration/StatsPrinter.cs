#nullable disable
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Newtonsoft.Json;

namespace DafnyTestGeneration {
  public class StatsPrinter {

    private readonly List<Dictionary<string, string>> accumulatedStats = new();

    private static string GetFullDafnyNameFromImpl(Implementation impl) {
      int endOfName = impl.VerboseName.IndexOf(' ');
      return impl.VerboseName[..endOfName];
    }

    public void WriteToFile(string filePath) {
      var json = JsonConvert.SerializeObject(
        accumulatedStats,
        Formatting.Indented);
      File.WriteAllText(filePath, json);
    }

    public void PopulateInformation(DafnyInfo dafnyInfo,
      HashSet<Implementation> implementations,
      Dictionary<Implementation, int> testCount,
      Dictionary<Implementation, int> failedTestCount) {
      foreach (var implementation in implementations) {
        Dictionary<string, string> record = new();
        record["blocks"] = implementation.Blocks
          .Count(block => block.Cmds.Count != 0).ToString();
        record["blocksCovered"] =
          ProgramModification.NOfBlocksCovered(implementation).ToString();
        record["blocksCoveredByTests"] =
          ProgramModification.NOfBlocksCovered(implementation, true).ToString();
        record["failedQueries"] =
          ProgramModification.NWithStatus(implementation,
            ProgramModification.Status.Failure).ToString();
        record["queries"] = (ProgramModification.NWithStatus(implementation,
                              ProgramModification.Status.Failure) +
                            ProgramModification.NWithStatus(
                              implementation,
                              ProgramModification.Status.Success)).ToString();
        record["tests"] =
          testCount.GetValueOrDefault(implementation, 0).ToString();
        record["failedTests"] = failedTestCount
          .GetValueOrDefault(implementation, 0).ToString();
        record["dafnyName"] = GetFullDafnyNameFromImpl(implementation);
        record["compiledName"] = dafnyInfo.GetCompiledName(record["dafnyName"]);
        accumulatedStats.Add(record);
      }
    }
  }
}