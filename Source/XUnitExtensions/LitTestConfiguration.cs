using System.Collections.Generic;
using System.Reflection;
using Xunit.Abstractions;

namespace XUnitExtensions {
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
  }
}