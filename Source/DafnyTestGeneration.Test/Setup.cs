using Microsoft.Dafny;

namespace DafnyTestGeneration.Test {

  public class Setup {

    public static void SetupDafnyOptions(string[] extraArgs = null) {
      var options = DafnyOptions.Create(extraArgs ?? System.Array.Empty<string>());
      options.DefiniteAssignmentLevel = 3;
      options.WarnShadowing = true;
      options.VerifyAllModules = true;
      options.LoopUnrollCount = 5;
      options.TestGenOptions.SeqLengthLimit = 3;
      options.TestGenOptions.Mode = TestGenerationOptions.Modes.Block;
      options.TestGenOptions.WarnDeadCode = false;
      options.TestGenOptions.TestInlineDepth = 0;
      options.TimeLimit = 10;
      DafnyOptions.Install(options);
    }

  }
}