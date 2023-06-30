using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test {

  public class Setup {


    public static DafnyOptions GetDafnyOptions(List<Action<DafnyOptions>> optionSettings, TextWriter writer, params string[] arguments) {
      var options = DafnyOptions.Create(writer, TextReader.Null, arguments ?? System.Array.Empty<string>());
      options.DefiniteAssignmentLevel = 3;
      options.WarnShadowing = true;
      options.VerifyAllModules = true;
      options.TestGenOptions.SeqLengthLimit = 3;
      options.TestGenOptions.Mode = TestGenerationOptions.Modes.Block;
      options.TestGenOptions.WarnDeadCode = false;
      options.TimeLimit = 10;
      foreach (var optionSetting in optionSettings) {
        optionSetting(options);
      }
      return options;
    }
    
    public static TheoryData<List<Action<DafnyOptions>>> EncodingConfigurations() {
      var theoryData = new TheoryData<List<Action<DafnyOptions>>>();
      theoryData.Add(new() { options => options.TypeEncodingMethod = CoreOptions.TypeEncoding.Arguments });
      theoryData.Add(new() { options => options.TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates });
      return theoryData;
    }
  }
}
