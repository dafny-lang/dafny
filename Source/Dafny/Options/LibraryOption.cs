using System.Collections.Generic;
using System.Linq;
using Dafny;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class LibraryOption : CommandLineOption<List<string>> {
  public static readonly LibraryOption Instance = new();

  public override object DefaultValue => new List<string>();
  public override string LongName => "library";
  public override string ShortName => null;
  public override string ArgumentName => null;
  public override string Category => "Compilation options";
  public override string Description => @"
The contents of this file and any files it includes can be referenced from other files as if they were included. 
However, these contents are skipped during code generation and verification.
This option is useful in a diamond dependency situation, 
to prevent code from the bottom dependency from being generated more than once.".TrimStart();

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    var value = Get(options) ?? new List<string>();
    if (ps.ConfirmArgumentCount(1)) {
      value.Add(ps.args[ps.i]);
    }

    Set(options, value);
  }

  public override string PostProcess(DafnyOptions options) {
    options.LibraryFiles = Get(options).ToHashSet();
    return null;
  }
}
