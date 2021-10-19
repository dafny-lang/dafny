using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {

  // TODO: Make safely immutable
  public class LitTestConfiguration {
    public Dictionary<string, string> Substitions { get; set; }

    public Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> Commands { get; set; }

    public IEnumerable<string> PassthroughEnvironmentVariables { get; set; }

    public string[] Features { get; set; }

    public string ApplySubstitutions(string s) {
      foreach (var (key, value) in Substitions) {
        s = s.Replace(key, value);
      }
      return s;
    }

    public LitTestConfiguration WithSubstitutions(Dictionary<string, string> more) {
      return new LitTestConfiguration {
        Substitions = Substitions.Concat(more).ToDictionary(pair => pair.Key, pair => pair.Value),
        Commands = Commands,
        PassthroughEnvironmentVariables = PassthroughEnvironmentVariables,
        Features = Features
      };
    }
  }
}