using System.Collections.Generic;

namespace XUnitExtensions {
  public class LitTestConfiguration {
    // Values are either strings or Assemblies (for our own CLI tools)
    public Dictionary<string, object> Substitions { get; set; }
    
    public bool InvokeMainMethodsDirectly { get; set; }
    
    public IEnumerable<string> PassthroughEnvironmentVariables { get; set; }

  }
}