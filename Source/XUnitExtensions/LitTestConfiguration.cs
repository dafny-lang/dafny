using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Microsoft.Boogie;
using Xunit.Abstractions;

namespace XUnitExtensions {
  
  // TODO: Make safely immutable
  public class LitTestConfiguration {
    public Dictionary<string, string> Substitions { get; set; }
    
    public Dictionary<string, (Assembly, string[])> MainMethodSubstitutions { get; set; }
    public bool InvokeMainMethodsDirectly { get; set; }

    public IEnumerable<string> PassthroughEnvironmentVariables { get; set; }

    public string ApplySubstitutions(string s) {
      foreach (var (key, value) in Substitions) {
        s = s.Replace(key, value);
      }
      return s;
    }

    public LitTestConfiguration WithSubsitutions(Dictionary<string, string> more) {
      return new LitTestConfiguration {
        Substitions = Substitions.Concat(more).ToDictionary(pair => pair.Key, pair => pair.Value),
        MainMethodSubstitutions = MainMethodSubstitutions,
        InvokeMainMethodsDirectly = InvokeMainMethodsDirectly,
        PassthroughEnvironmentVariables = PassthroughEnvironmentVariables
      };
    }
  }
}