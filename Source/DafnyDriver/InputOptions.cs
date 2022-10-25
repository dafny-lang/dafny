using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class InputsOption : CommandLineOption<IEnumerable<string>> {
  public static readonly InputsOption Instance = new();
  public override object DefaultValue => new List<string>();
  public override string LongName => "input";
  public override string ArgumentName => "file";
  public override string Description => "Specify an additional input file.";

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    throw new InvalidOperationException();
  }

  public override string PostProcess(DafnyOptions options) {
    foreach (var file in Get(options)) {
      options.AddFile(file);
    }

    return null;
  }
}