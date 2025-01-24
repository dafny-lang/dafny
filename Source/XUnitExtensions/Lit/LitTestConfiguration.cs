using System;
using System.Collections.Generic;
using System.Linq;

namespace XUnitExtensions.Lit {

  // TODO: Make safely immutable
  public class LitTestConfiguration {
    // Values can be either a string or an IEnumerable<string>
    public readonly Dictionary<string, object> Substitutions;

    public readonly Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> Commands;

    public readonly string[] Features;

    public readonly IEnumerable<string> PassthroughEnvironmentVariables;

    public LitTestConfiguration(Dictionary<string, object> substitutions,
            Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> commands,
            string[] features,
            IEnumerable<string> passthroughEnvironmentVariables) {
      Substitutions = substitutions;
      Commands = commands;
      Features = features;
      PassthroughEnvironmentVariables = passthroughEnvironmentVariables;
    }

    public IEnumerable<string> ApplySubstitutions(string s) {
      if (Substitutions.TryGetValue(s, out var result)) {
        if (result is IEnumerable<string> enumerable) {
          return enumerable;
        }

        return new[] { (string)result };
      }

      foreach (var (key, value) in Substitutions) {
        if (value is string stringValue) {
          s = s.Replace(key, stringValue);
        }
      }
      return new[] { s };
    }

    public LitTestConfiguration WithSubstitutions(Dictionary<string, object> more) {
      return new LitTestConfiguration(
        Substitutions.Concat(more).ToDictionary(pair => pair.Key, pair => pair.Value),
        Commands,
        Features,
        PassthroughEnvironmentVariables
      );
    }
  }
}