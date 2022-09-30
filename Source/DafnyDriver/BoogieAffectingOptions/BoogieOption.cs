using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class BoogieOption : StringOption {
  public static readonly BoogieOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "boogie";
  public override string ArgumentName => "arguments";
  public override string Description => "Specify arguments that are passed to Boogie, a tool used to verify Dafny programs.";

  public override string PostProcess(DafnyOptions options) {
    var boogieOptions = Get(options);
    if (boogieOptions != null) {
      options.Parse(SplitArguments(boogieOptions).ToArray());
    }
    return null;
  }

  private static IReadOnlyList<string> SplitArguments(string commandLine) {
    var inSingleQuote = false;
    var inDoubleQuote = false;
    var result = new List<string>();
    var start = 0;
    for (var end = 0; end < commandLine.Length; end++) {
      var store = false;
      if (commandLine[end] == '"' && !inSingleQuote) {
        store = inDoubleQuote;
        inDoubleQuote = !inDoubleQuote;
      }
      if (commandLine[end] == '\'' && !inDoubleQuote) {
        store = inSingleQuote;
        inSingleQuote = !inSingleQuote;
      }
      if (!inSingleQuote && !inDoubleQuote && commandLine[end] == ' ') {
        store = true;
      }

      if (store) {
        result.Add(commandLine.Substring(start, end - start));
        start = end + 1; // Skip the single or double quote or space in the next entry
      }
    }
    result.Add(commandLine.Substring(start, commandLine.Length - start));
    return result;
  }
}
