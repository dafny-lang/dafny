using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class UnsupportedCommand : ILitCommand {

    public static UnsupportedCommand Parse(string line, LitTestConfiguration config) {
      var features = line.Split(",", StringSplitOptions.RemoveEmptyEntries).Select(s => s.Trim());
      return new UnsupportedCommand(features);
    }

    public IEnumerable<string> Features { get; }

    public UnsupportedCommand(IEnumerable<string> features) {
      Features = features;
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      return (0, "", "");
    }
  }
}