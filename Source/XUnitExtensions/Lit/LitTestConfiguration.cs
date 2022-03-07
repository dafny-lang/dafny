using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {

  // TODO: Make safely immutable
  public class LitTestConfiguration {
    public readonly Dictionary<string, string> Substitutions;

    public readonly Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> Commands;

    public readonly string[] Features;

    public readonly IEnumerable<string> PassthroughEnvironmentVariables;

    public LitTestConfiguration(Dictionary<string, string> substitutions,
            Dictionary<string, Func<IEnumerable<string>, LitTestConfiguration, ILitCommand>> commands,
            string[] features,
            IEnumerable<string> passthroughEnvironmentVariables) {
      Substitutions = substitutions;
      Commands = commands;
      Features = features;
      PassthroughEnvironmentVariables = passthroughEnvironmentVariables;
    }

    public string ApplySubstitutions(string s) {
      foreach (var (key, value) in Substitutions) {
        s = s.Replace(key, value);
      }
      return s;
    }

    public LitTestConfiguration WithSubstitutions(Dictionary<string, string> more) {
      return new LitTestConfiguration(
        Substitutions.Concat(more).ToDictionary(pair => pair.Key, pair => pair.Value),
        Commands,
        Features,
        PassthroughEnvironmentVariables
      );
    }
  }
}